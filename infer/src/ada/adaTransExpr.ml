(*
 * Copyright (c) 2017-present, AdaCore.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 *)

open! IStd
open Libadalang
open AdaFrontend
open AdaTransType
open Option.Monad_infix
module L = Logging

let rec mk_not exp =
  let open Exp in
  match exp with
  | UnOp (Unop.LNot, exp, _) ->
      exp
  | BinOp (Lt, lhs, rhs) ->
      BinOp (Ge, lhs, rhs)
  | BinOp (Gt, lhs, rhs) ->
      BinOp (Le, lhs, rhs)
  | BinOp (Le, lhs, rhs) ->
      BinOp (Gt, lhs, rhs)
  | BinOp (Ge, lhs, rhs) ->
      BinOp (Lt, lhs, rhs)
  | BinOp (LAnd, lhs, rhs) ->
      BinOp (LOr, mk_not lhs, mk_not rhs)
  | BinOp (LOr, lhs, rhs) ->
      BinOp (LAnd, mk_not lhs, mk_not rhs)
  | _ ->
      UnOp (Unop.LNot, exp, Some Typ.(mk (Tint IBool)))


let type_of_expr ctx expr =
  match Expr.p_expression_type expr with
  | Some typ ->
      trans_type_decl ctx.tenv typ
  | None ->
      (* No type. We concider that the expression have the type void *)
      Typ.void


let trans_dest ctx dest =
  let rec aux = function
    | (#Identifier.t | #DottedName.t) as name ->
        ([], Exp.Lvar (pvar ctx name))
    | `ExplicitDeref {ExplicitDerefType.f_prefix= (lazy prefix)} ->
        let instrs, dest_expr = aux prefix in
        let id = Ident.(create_fresh knormal) in
        let load =
          Sil.Load (id, dest_expr, type_of_expr ctx prefix, location ctx.source_file dest)
        in
        (instrs @ [load], Exp.Var id)
    | _ as expr ->
        unimplemented "trans_dest for %s" (AdaNode.short_image expr)
  in
  aux
    ( dest
      :> [ AttributeRef.t
         | CallExpr.t
         | CharLiteral.t
         | DottedName.t
         | ExplicitDeref.t
         | Identifier.t
         | QualExpr.t
         | StringLiteral.t
         | TargetName.t
         | UpdateAttributeRef.t ] )


(** The translation of an expression can either be a simple expression with
 * Some instructions, in that case Exp is used. Or an If expression with an
 * expression being the one tested and true/false branches *)
type simple_expr = Exp of Sil.instr list * Exp.t | Bool of bool

type expr = SimpleExpr of simple_expr | If of Sil.instr list * Exp.t * (expr * expr)

let of_exp instrs exp = SimpleExpr (Exp (instrs, exp))

let of_bool b = SimpleExpr (Bool b)

let to_exp = function Exp (instrs, exp) -> (instrs, exp) | Bool b -> ([], Exp.bool b)

(** A value of this type is passed to the translation of the expression. It says
 * what will be done with the translated expression.
 *    - Goto is meaningfull only for boolean expressions. The expression is
 *       translated to different branches in which the expression is evaluated to
 *       true or false. At the end of each branch in which the expression is evaluated
 *       to true, there is a goto to the first label, and the second label for false.
 *
 *    - Tmp means that the caller wants the result of the expression to be in
 *       an tmp variable if necessary. It is necessary when the expression makes
 *       some control flow.
 *
 *    - Inline means that the caller will use the expression as it is. This means
 *       that for example, for one assignment, the assignment could be duplicated
 *       if some control flow happened. *)
type _ continuation =
  | Goto : jump_kind * jump_kind -> unit continuation
  | Tmp : string -> (Sil.instr list * Exp.t) continuation
  | Inline : expr continuation

(** Calls the function f, on all leaf of the structured expression. This recreates
 * a structured expression by expanding the leafs with the result of calling f *)
let rec map ~f expr_result =
  match expr_result with
  | SimpleExpr simple_expr ->
      f simple_expr
  | If (instrs, expr, (true_b, false_b)) ->
      If (instrs, expr, (map ~f true_b, map ~f false_b))


(** transform an expression to a list of statements by calling f on the leafs *)
let rec map_to_stmts ~f ~orig_node ctx expr_result =
  let rec aux expr_result =
    match expr_result with
    | SimpleExpr simple_expr ->
        f simple_expr
    | If (instrs, exp, (true_b, false_b)) ->
        let loc = location ctx.source_file orig_node in
        let prune_true = Sil.(Prune (exp, loc, true, Ik_land_lor)) in
        let prune_false = Sil.(Prune (mk_not exp, loc, false, Ik_land_lor)) in
        let true_nodekind =
          Procdesc.Node.(Prune_node (true, Sil.Ik_land_lor, PruneNodeKind_TrueBranch))
        in
        let false_nodekind =
          Procdesc.Node.(Prune_node (false, Sil.Ik_land_lor, PruneNodeKind_FalseBranch))
        in
        let prune_true_stmt =
          Block {instrs= instrs @ [prune_true]; loc; nodekind= true_nodekind}
        in
        let prune_false_stmt =
          Block {instrs= instrs @ [prune_false]; loc; nodekind= false_nodekind}
        in
        let then_b = aux true_b in
        let else_b = aux false_b in
        [Split (loc, [prune_true_stmt :: then_b; prune_false_stmt :: else_b])]
  in
  aux expr_result


(** Depending on the wanted continuation, returns a structured result.
 *    - Goto: creates true and false branches with the expression
 *       pruned to true/false.
 *    - Tmp/Inline: simply return the given stmts/instructions and expression *)
let return : type a.
    context -> a continuation -> [< AdaNode.t] -> Typ.t -> stmt list -> expr -> stmt list * a =
 fun ctx cont orig_node typ stmts expr ->
  let loc = location ctx.source_file orig_node in
  match cont with
  | Goto (jump_true, jump_false) ->
      let rec f = function
        | Exp (instrs, exp) ->
            (* In this case we create a if expression with one branch where the
           * expression is true, and false in the other branch *)
            map_to_stmts ~f ~orig_node ctx (If (instrs, exp, (of_bool true, of_bool false)))
        | Bool b ->
            [Jump (loc, if b then jump_true else jump_false)]
      in
      (stmts @ map_to_stmts ~f ~orig_node ctx expr, ())
  | Tmp name -> (
    match expr with
    | SimpleExpr simple_expr ->
        (* Do not insert a temporary if it is not usefull *)
        (stmts, to_exp simple_expr)
    | _ ->
        let tmp_var = Pvar.mk_tmp name (Procdesc.get_proc_name ctx.proc_desc) in
        let rec f simple_expr =
          let instrs, exp = to_exp simple_expr in
          let assignment = Sil.Store (Exp.Lvar tmp_var, typ, exp, loc) in
          let block =
            {instrs= instrs @ [assignment]; loc; nodekind= Procdesc.Node.Stmt_node (Call "assign")}
          in
          [Block block]
        in
        let id = Ident.(create_fresh knormal) in
        let load = Sil.Load (id, Exp.Lvar tmp_var, typ, loc) in
        (stmts @ map_to_stmts ~f ~orig_node ctx expr, ([load], Exp.Var id)) )
  | Inline ->
      (stmts, expr)


let combine ~f lhs_expr rhs_expr =
  (* To combine two expressions lhs and rhs, we append the rhs expression to
   * all the lhs leafs and we call f with the actual instructions and expressions *)
  let aux lhs_simple_expr =
    let lhs_instrs, lhs_exp = to_exp lhs_simple_expr in
    let call_f rhs_simple_expr =
      let rhs_instrs, rhs_exp = to_exp rhs_simple_expr in
      of_exp (lhs_instrs @ rhs_instrs) (f lhs_exp rhs_exp)
    in
    map ~f:call_f rhs_expr
  in
  map ~f:aux lhs_expr


let mk_or lhs_expr rhs_expr =
  (* Make a shortcircuit or from the two given expressions *)
  let f = function
    | Bool true ->
        of_bool true
    | Bool false ->
        rhs_expr
    | Exp (instrs, exp) ->
        If (instrs, exp, (of_bool true, rhs_expr))
  in
  map ~f lhs_expr


let mk_and lhs_expr rhs_expr =
  (* Make a shortcircuit and from the two given expressions *)
  let f = function
    | Bool false ->
        of_bool false
    | Bool true ->
        rhs_expr
    | Exp (instrs, exp) ->
        If (instrs, exp, (rhs_expr, of_bool false))
  in
  map ~f lhs_expr


let rec trans_binop : type a. context -> a continuation -> BinOp.t -> stmt list * a =
 fun ctx cont binop ->
  let lhs = BinOp.f_left binop in
  let rhs = BinOp.f_right binop in
  let simple_binop op =
    let f lhs_exp rhs_exp = Exp.BinOp (op, lhs_exp, rhs_exp) in
    combine ~f
  in
  let lhs_stmts, lhs_expr_res = trans_expr_ ctx Inline (lhs :> Expr.t) in
  let rhs_stmts, rhs_expr_res = trans_expr_ ctx Inline (rhs :> Expr.t) in
  let inlined_result =
    match BinOp.f_op binop with
    | `OpAnd _ ->
        simple_binop Binop.LAnd lhs_expr_res rhs_expr_res
    | `OpAndThen _ ->
        mk_and lhs_expr_res rhs_expr_res
    | `OpOr _ ->
        simple_binop Binop.LOr lhs_expr_res rhs_expr_res
    | `OpOrElse _ ->
        mk_or lhs_expr_res rhs_expr_res
    | `OpXor _ ->
        simple_binop Binop.BXor lhs_expr_res rhs_expr_res
    | `OpEq _ ->
        simple_binop Binop.Eq lhs_expr_res rhs_expr_res
    | `OpGt _ ->
        simple_binop Binop.Gt lhs_expr_res rhs_expr_res
    | `OpGte _ ->
        simple_binop Binop.Ge lhs_expr_res rhs_expr_res
    | `OpLt _ ->
        simple_binop Binop.Lt lhs_expr_res rhs_expr_res
    | `OpLte _ ->
        simple_binop Binop.Le lhs_expr_res rhs_expr_res
    | `OpMinus _ ->
        simple_binop (Binop.MinusA None) lhs_expr_res rhs_expr_res
    | `OpMod _ ->
        simple_binop Binop.Mod lhs_expr_res rhs_expr_res
    | `OpMult _ ->
        simple_binop (Binop.Mult None) lhs_expr_res rhs_expr_res
    | `OpNeq _ ->
        simple_binop Binop.Ne lhs_expr_res rhs_expr_res
    | `OpPlus _ ->
        simple_binop (Binop.PlusA None) lhs_expr_res rhs_expr_res
    | `OpDiv _ ->
        simple_binop Binop.Div lhs_expr_res rhs_expr_res
    | _ as op ->
        unimplemented "BinOp op for %s" (AdaNode.short_image op)
  in
  return ctx cont binop (type_of_expr ctx binop) (lhs_stmts @ rhs_stmts) inlined_result


and trans_enum_literal : type a.
    context -> a continuation -> Typ.t -> EnumLiteralDecl.t -> stmt list * a =
 fun ctx cont typ enum_lit ->
  (* Here we translate an enum literal to an integer. But we don't care about the
   * representation. This means that the returned integer is not equivalent to
   * calling 'Pos in Ada *)
  let enum_typ =
    match EnumLiteralDecl.p_enum_type enum_lit with
    | Some typ ->
        typ
    | None ->
        L.die InternalError "Cannot find enum type for %s" (AdaNode.short_image enum_lit)
  in
  match TypeDecl.f_type_def enum_typ with
  | `EnumTypeDef {f_enum_literals= (lazy (`EnumLiteralDeclList {list= (lazy enum_literals)}))} -> (
      (* Find the position of the enum literal inside the type it is associated to *)
      let result = List.findi ~f:(fun _ lit -> EnumLiteralDecl.equal enum_lit lit) enum_literals in
      match result with
      | Some (pos, _) ->
          return ctx cont enum_lit typ [] (of_exp [] (Exp.Const (Const.Cint (IntLit.of_int pos))))
      | None ->
          L.die InternalError "Cannot find the enum literal %s for type %s"
            (AdaNode.short_image enum_lit) (AdaNode.short_image enum_typ) )
  | _ ->
      L.die InternalError "TypeDecl for %s should be an EnumTypeDef" (AdaNode.short_image enum_typ)


and trans_call : type a.
       context
    -> a continuation
    -> [< AdaNode.t]
    -> [< BasicDecl.t]
    -> [< Expr.t] list
    -> stmt list * a =
 fun ctx cont call call_ref args ->
  match call_ref with
  | #EnumLiteralDecl.t as enum_lit ->
      (* An enum literal is a call in Ada *)
      trans_enum_literal ctx cont (type_of_expr ctx call) enum_lit
  | #BaseSubpBody.t as subp ->
      (* For a call to a subprogram, we generate the Sil instruction *)
      let loc = location ctx.source_file call in
      let typ = type_of_expr ctx call in
      let proc_name = get_proc_name subp in
      let f (stmts, instrs, args) expr =
        let arg_stmts, (arg_instrs, arg_expr) = trans_expr_ ctx (Tmp "arg") (expr :> Expr.t) in
        let typ_arg = type_of_expr ctx expr in
        (stmts @ arg_stmts, instrs @ arg_instrs, args @ [(arg_expr, typ_arg)])
      in
      let stmts, instrs, args = List.fold_left ~f ~init:([], [], []) args in
      let id = Ident.(create_fresh knormal) in
      let sil_call =
        Sil.Call ((id, typ), Exp.Const (Const.Cfun proc_name), args, loc, CallFlags.default)
      in
      return ctx cont call typ stmts (of_exp (instrs @ [sil_call]) (Exp.Var id))
  | _ ->
      unimplemented "trans_call for %s" (AdaNode.short_image call_ref)


and trans_bounds_ ctx bounds_expr =
  match bounds_expr with
  | #Expr.t as expr -> (
    match (expr : [< Expr.t]) with
    | `BinOp {f_op= (lazy (`OpDoubleDot _)); f_left= (lazy left); f_right= (lazy right)}
    | `RelationOp {f_op= (lazy (`OpDoubleDot _)); f_left= (lazy left); f_right= (lazy right)} ->
        let low_bound_stmts, (low_bound_instrs, low_bound) =
          trans_expr_ ctx (Tmp "") (left :> Expr.t)
        in
        let high_bound_stmts, (high_bound_instrs, high_bound) =
          trans_expr_ ctx (Tmp "") (right :> Expr.t)
        in
        ( low_bound_stmts @ high_bound_stmts
        , low_bound_instrs @ high_bound_instrs
        , low_bound
        , high_bound )
    | (#Identifier.t | #DottedName.t) as ident ->
        let stmts, (instrs, exp) = trans_expr_ ctx (Tmp "") (ident :> Expr.t) in
        (stmts, instrs, exp, exp)
    | _ ->
        unimplemented "trans_bounds for %s" (AdaNode.short_image bounds_expr) )
  | #DiscreteSubtypeIndication.t ->
      unimplemented "trans_bounds for %s" (AdaNode.short_image bounds_expr)


and trans_membership_expr_ : type a.
       context
    -> a continuation
    -> AdaNode.t
    -> Typ.t
    -> expr
    -> [Expr.t | DiscreteSubtypeIndication.t] list
    -> stmt list * a =
 fun ctx cont orig_node typ expr alternatives ->
  let trans_alternative alt =
    let choice_stmts, choice_instrs, low_bound, high_bound =
      trans_bounds_ ctx (alt :> [Expr.t | DiscreteSubtypeIndication.t])
    in
    let comparison simple_expr =
      let instrs, exp = to_exp simple_expr in
      let comp_exp =
        if Exp.equal low_bound high_bound then Exp.eq exp low_bound
        else Exp.BinOp (Binop.LAnd, Exp.le low_bound exp, Exp.le exp high_bound)
      in
      of_exp (choice_instrs @ instrs) comp_exp
    in
    (choice_stmts, map ~f:comparison expr)
  in
  let f (acc_stmts, acc_expr) choice =
    let choice_stmts, choice_expr = trans_alternative choice in
    (acc_stmts @ choice_stmts, mk_or acc_expr choice_expr)
  in
  (* For each choice of the list, make an or expression of all comparisons *)
  let final_stmts, final_expr = List.fold_left ~f ~init:([], of_bool false) alternatives in
  return ctx cont orig_node typ final_stmts final_expr


and trans_expr_ : type a. context -> a continuation -> Expr.t -> stmt list * a =
 fun ctx cont expr ->
  let typ = type_of_expr ctx expr in
  let loc = location ctx.source_file expr in
  match (expr :> Expr.t) with
  | #IntLiteral.t as int_literal ->
      let value = IntLiteral.p_denoted_value int_literal in
      return ctx cont expr typ [] (of_exp [] (Exp.Const (Const.Cint (IntLit.of_int value))))
  | (#Identifier.t | #DottedName.t) as ident when Name.p_is_call ident -> (
    match Name.p_referenced_decl ident with
    | Some call_ref ->
        trans_call ctx cont ident call_ref []
    | _ ->
        unimplemented "trans_expr for an identifier call %s" (AdaNode.short_image ident) )
  | (#Identifier.t | #DottedName.t) as name ->
      let stmts, dest = trans_dest ctx name in
      let id = Ident.(create_fresh knormal) in
      let load = Sil.Load (id, dest, typ, loc) in
      return ctx cont expr typ [] (of_exp (stmts @ [load]) (Exp.Var id))
  | `AttributeRef {f_prefix= (lazy prefix); f_attribute= (lazy attribute)}
  | `UpdateAttributeRef {f_prefix= (lazy prefix); f_attribute= (lazy attribute)}
    when is_access attribute ->
      let dest_instrs, dest = trans_dest ctx prefix in
      return ctx cont expr typ [] (of_exp dest_instrs dest)
  | #BinOp.t as binop -> (
      let lhs = BinOp.f_left binop in
      let op = BinOp.f_op binop in
      let rhs = BinOp.f_right binop in
      match Name.p_referenced_decl op with
      | Some ref ->
          trans_call ctx cont binop ref ([lhs; rhs] :> Expr.t list)
      | None ->
          trans_binop ctx cont binop )
  | `CallExpr {f_name= (lazy name); f_suffix= (lazy (#AssocList.t as assoc_list))} as call_expr
    when Name.p_is_call call_expr -> (
      let sorted_params = AssocList.p_zip_with_params assoc_list |> sort_params ctx.proc_desc in
      match Name.p_referenced_decl name with
      | Some ref ->
          trans_call ctx cont expr ref sorted_params
      | None ->
          L.die InternalError "Unknown call to %s" (AdaNode.short_image name) )
  | `MembershipExpr
      { f_expr= (lazy expr)
      ; f_op= (lazy op)
      ; f_membership_exprs= (lazy (`ExprAlternativesList {list= (lazy alternatives)})) } ->
      let typ = type_of_expr ctx expr in
      let tested_stmts, tested_expr = trans_expr_ ctx Inline (expr :> Expr.t) in
      let membership_stmts, membership_expr =
        trans_membership_expr_ ctx Inline
          (expr :> AdaNode.t)
          typ tested_expr
          (alternatives :> [Expr.t | DiscreteSubtypeIndication.t] list)
      in
      let inlined_expr =
        match op with
        | `OpIn _ ->
            membership_expr
        | `OpNotIn _ ->
            let f simple_expr =
              match simple_expr with
              | Bool b ->
                  of_bool (not b)
              | Exp (instrs, exp) ->
                  of_exp instrs (mk_not exp)
            in
            map ~f membership_expr
      in
      return ctx cont expr typ (tested_stmts @ membership_stmts) inlined_expr
  | `ParenExpr {f_expr= (lazy expr)} ->
      trans_expr_ ctx cont (expr :> Expr.t)
  | _ as expr ->
      unimplemented "trans_expr for %s" (AdaNode.short_image expr)


let trans_expr ctx cont expr = trans_expr_ ctx cont (expr :> Expr.t)

let trans_bounds ctx bounds_expr =
  trans_bounds_ ctx (bounds_expr :> [Expr.t | DiscreteSubtypeIndication.t])


and trans_membership_expr ctx cont orig_node typ expr alternatives =
  trans_membership_expr_ ctx cont
    (orig_node :> AdaNode.t)
    typ expr
    (alternatives :> [Expr.t | DiscreteSubtypeIndication.t] list)
