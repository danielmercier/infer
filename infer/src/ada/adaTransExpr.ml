(*
 * Copyright (c) 2017-present, AdaCore.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 *)

open! IStd
open Libadalang
open LalUtils
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
  | BinOp (Eq, lhs, rhs) ->
      BinOp (Ne, lhs, rhs)
  | BinOp (Ne, lhs, rhs) ->
      BinOp (Eq, lhs, rhs)
  | _ when Exp.equal exp (Exp.bool true) ->
      Exp.bool false
  | _ when Exp.equal exp (Exp.bool false) ->
      Exp.bool true
  | _ ->
      UnOp (Unop.LNot, exp, Some Typ.(mk (Tint IBool)))


let type_of_expr ctx expr =
  match Expr.p_expression_type expr with
  | Some typ ->
      trans_type_decl ctx.tenv typ
  | None ->
      (* No type. We concider that the expression have the type void *)
      Typ.void


let record_field name =
  match Name.p_referenced_decl name with
  | Some ((#ComponentDecl.t | #DiscriminantSpec.t) as field) ->
      Some field
  | _ ->
      None


let load typ loc exp =
  let id = Ident.(create_fresh knormal) in
  let load = Sil.Load (id, exp, typ, loc) in
  ([load], Exp.Var id)


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
let rec map_to_stmts ~f loc expr_result =
  let rec aux expr_result =
    match expr_result with
    | SimpleExpr simple_expr ->
        f simple_expr
    | If (instrs, exp, (true_b, false_b)) ->
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
    context -> a continuation -> Typ.t -> Location.t -> stmt list -> expr -> stmt list * a =
 fun ctx cont typ loc stmts expr ->
  match cont with
  | Goto (jump_true, jump_false) ->
      let rec f = function
        | Exp (instrs, exp) ->
            (* In this case we create a if expression with one branch where the
           * expression is true, and false in the other branch *)
            map_to_stmts ~f loc (If (instrs, exp, (of_bool true, of_bool false)))
        | Bool b ->
            [Jump (loc, if b then jump_true else jump_false)]
      in
      (stmts @ map_to_stmts ~f loc expr, ())
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
        (stmts @ map_to_stmts ~f loc expr, ([load], Exp.Var id)) )
  | Inline ->
      (stmts, expr)


let combine ~f lhs_expr rhs_expr =
  (* To combine two expressions lhs and rhs, we append the rhs expression to
   * all the lhs leafs and we call f with the actual instructions and expressions *)
  let aux lhs_simple_expr =
    let lhs_instrs, lhs_exp = to_exp lhs_simple_expr in
    let call_f rhs_simple_expr =
      let rhs_instrs, rhs_exp = to_exp rhs_simple_expr in
      let f_instrs, f_exp = f lhs_exp rhs_exp in
      of_exp (lhs_instrs @ rhs_instrs @ f_instrs) f_exp
    in
    map ~f:call_f rhs_expr
  in
  map ~f:aux lhs_expr


let mk_if cond_expr then_expr else_expr =
  (* Create an if expression by going to the leafs of the condition expression
   * and create an If there with then_expr as the then branch and else_expr as
   * then else branch *)
  let f = function
    | Bool true ->
        then_expr
    | Bool false ->
        else_expr
    | Exp (instrs, exp) ->
        If (instrs, exp, (then_expr, else_expr))
  in
  map ~f cond_expr


let mk_or lhs_expr rhs_expr =
  (* Make a shortcircuit or from the two given expressions *)
  mk_if lhs_expr (of_bool true) rhs_expr


let mk_and lhs_expr rhs_expr =
  (* Make a shortcircuit and from the two given expressions *)
  mk_if lhs_expr rhs_expr (of_bool false)


let mk_load typ loc expr =
  let f simple_expr =
    let instrs, exp = to_exp simple_expr in
    let load_instrs, load_exp = load typ loc exp in
    of_exp (instrs @ load_instrs) load_exp
  in
  map ~f expr


(* Type used to call mk_array_access to access a field of the array or an index 
 * Use a GADT because when accessing an index, we need setup instructions *)
type _ array_access =
  | Index : Exp.t -> (Sil.instr list * Exp.t) array_access
  | Data : Exp.t array_access
  | First : Exp.t array_access
  | Last : Exp.t array_access
  | Length : Exp.t array_access

let rec mk_array_access : type a. context -> Typ.t -> Location.t -> Exp.t -> a array_access -> a =
 fun ctx array_typ loc prefix array_access ->
  (* An array is translated to a record with fields for first, last and the data.
   * This function should be use to access the fields of the record *)
  let int_typ = Typ.(mk (Tint IInt)) in
  let data_field_name = Typ.Fieldname.Ada.from_string "data" in
  let real_array_typ =
    let lookup = Tenv.lookup ctx.tenv in
    Typ.Struct.fld_typ ~lookup ~default:Typ.void data_field_name array_typ
  in
  match array_access with
  | Index exp ->
      let field = mk_array_access ctx array_typ loc prefix Data in
      let load_instrs, load_exp = load real_array_typ loc field in
      (load_instrs, Exp.Lindex (load_exp, exp))
  | Data ->
      Exp.Lfield (prefix, data_field_name, real_array_typ)
  | First ->
      Exp.Lfield (prefix, Typ.Fieldname.Ada.from_string "first", int_typ)
  | Last ->
      Exp.Lfield (prefix, Typ.Fieldname.Ada.from_string "last", int_typ)
  | Length ->
      Exp.Lfield (prefix, Typ.Fieldname.Ada.from_string "length", int_typ)


let rec trans_lvalue_ ctx dest =
  match (dest :> lvalue) with
  | `DottedName {f_prefix= (lazy prefix); f_suffix= (lazy suffix)} as name -> (
    match record_field suffix with
    | Some _ ->
        let prefix_stmts, (prefix_instrs, prefix_expr) = trans_lvalue_ ctx prefix in
        ( prefix_stmts
        , ( prefix_instrs
          , Exp.Lfield
              ( prefix_expr
              , field_name (Option.value_exn (AdaNode.p_xref name))
              , type_of_expr ctx name ) ) )
    | None ->
        ([], ([], Exp.Lvar (pvar ctx name))) )
  | `Identifier _ as name -> (
      let typ = type_of_expr ctx name in
      let defining_name = Option.value_exn (AdaNode.p_xref name) in
      let dest_expr = Exp.Lvar (pvar ctx name) in
      match DefiningNameMap.find_opt defining_name ctx.params_modes with
      | Some Reference ->
          let ptr_typ = Typ.(mk (Tptr (typ, Pk_reference))) in
          ([], load ptr_typ (location ctx.source_file name) dest_expr)
      | Some Copy | None ->
          ([], ([], dest_expr)) )
  | `ExplicitDeref {ExplicitDerefType.f_prefix= (lazy prefix)} ->
      let stmts, (instrs, dest_expr) = trans_lvalue_ ctx prefix in
      let load_instrs, load_expr =
        load (type_of_expr ctx prefix) (location ctx.source_file dest) dest_expr
      in
      (stmts, (instrs @ load_instrs, load_expr))
  | `CallExpr {f_name= (lazy name); f_suffix= (lazy (`AssocList {list= (lazy assoc_list)}))} ->
      (* Since we are evaluating an lvalue, consider this as an access to an
       * array. An array is compiled to a record with the field data being the
       * real array. *)
      let array_typ = type_of_expr ctx name in
      let array_dest_stmts, (array_dest_instrs, array_dest) = trans_lvalue_ ctx name in
      (* The destination of the array should be loaded to get it's base address *)
      let index_dest_stmts, (index_dest_instrs, index_dest) =
        match assoc_list with
        | [`ParamAssoc {f_designator= (lazy None); f_r_expr= (lazy index_expr)}] ->
            trans_expr_ ctx (Tmp "index") (index_expr :> Expr.t)
        | _ ->
            unimplemented "trans_lvalue for a CallExpr for assoc_list other than one ParamAssoc"
      in
      let array_access_instrs, array_access =
        mk_array_access ctx array_typ (location ctx.source_file name) array_dest (Index index_dest)
      in
      ( array_dest_stmts @ index_dest_stmts
      , (array_dest_instrs @ index_dest_instrs @ array_access_instrs, array_access) )
  | `CallExpr {f_suffix= (lazy suffix)} ->
      unimplemented "trans_lvalue for CallExpr with suffix %s" (AdaNode.short_image suffix)
  | _ as expr ->
      unimplemented "trans_lvalue for %s" (AdaNode.short_image expr)


and trans_binop : type a. context -> a continuation -> BinOp.t -> stmt list * a =
 fun ctx cont binop ->
  let lhs = BinOp.f_left binop in
  let rhs = BinOp.f_right binop in
  let simple_binop op =
    let f lhs_exp rhs_exp = ([], Exp.BinOp (op, lhs_exp, rhs_exp)) in
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
  let typ = type_of_expr ctx binop in
  let loc = location ctx.source_file binop in
  return ctx cont typ loc (lhs_stmts @ rhs_stmts) inlined_result


and trans_unop : type a. context -> a continuation -> UnOp.t -> stmt list * a =
 fun ctx cont unop ->
  let typ = type_of_expr ctx unop in
  let loc = location ctx.source_file unop in
  let op = UnOp.f_op unop in
  let stmts, expr = trans_expr_ ctx Inline (UnOp.f_expr unop :> Expr.t) in
  match op with
  | `OpPlus _ ->
      return ctx cont typ loc stmts expr
  | `OpMinus _ ->
      return ctx cont typ loc stmts
        (map
           ~f:(fun simple_expr ->
             let instrs, exp = to_exp simple_expr in
             of_exp instrs (Exp.UnOp (Unop.Neg, exp, Some typ)) )
           expr)
  | `OpNot _ ->
      return ctx cont typ loc stmts
        (map
           ~f:(function
             | Bool b ->
                 of_bool (not b)
             | Exp (instrs, exp) ->
                 of_exp instrs (Exp.UnOp (Unop.LNot, exp, Some typ)) )
           expr)
  | `OpAbs _ ->
      (* Translate a call to abs to an if expression,
       * abs x is
       *    if 0 <= x then x else -x *)
      return ctx cont typ loc stmts
        (map
           ~f:(fun simple_expr ->
             let instrs, exp = to_exp simple_expr in
             If
               ( instrs
               , Exp.le Exp.zero exp
               , (of_exp instrs exp, of_exp instrs (Exp.UnOp (Unop.Neg, exp, Some typ))) ) )
           expr)


and trans_enum_literal : type a.
    context -> a continuation -> Typ.t -> Location.t -> EnumLiteralDecl.t -> stmt list * a =
 fun ctx cont typ loc enum_lit ->
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
          return ctx cont typ loc [] (of_exp [] (Exp.Const (Const.Cint (IntLit.of_int pos))))
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
    -> (param_mode * [< Expr.t]) list
    -> stmt list * a =
 fun ctx cont call call_ref args ->
  let loc = location ctx.source_file call in
  let typ = type_of_expr ctx call in
  match call_ref with
  | #EnumLiteralDecl.t as enum_lit ->
      (* An enum literal is a call in Ada *)
      trans_enum_literal ctx cont typ loc enum_lit
  | #BaseSubpBody.t as subp ->
      (* For a call to a subprogram, we generate the Sil instruction *)
      let proc_name = get_proc_name subp in
      let f (stmts, instrs, args) (mode, expr) =
        let arg_stmts, (arg_instrs, arg_expr) =
          match mode with
          | Copy ->
              trans_expr_ ctx (Tmp "arg") (expr :> Expr.t)
          | Reference -> (
            match (expr :> Expr.t) with
            | #lvalue as lvalue ->
                trans_lvalue_ ctx lvalue
            | _ ->
                L.die InternalError "out parameter should be an lvalue" )
        in
        let typ_arg =
          match mode with
          | Copy ->
              type_of_expr ctx expr
          | Reference ->
              Typ.(mk (Tptr (type_of_expr ctx expr, Pk_reference)))
        in
        (stmts @ arg_stmts, instrs @ arg_instrs, args @ [(arg_expr, typ_arg)])
      in
      let stmts, instrs, args = List.fold_left ~f ~init:([], [], []) args in
      let id = Ident.(create_fresh knormal) in
      let sil_call =
        Sil.Call ((id, typ), Exp.Const (Const.Cfun proc_name), args, loc, CallFlags.default)
      in
      return ctx cont typ loc stmts (of_exp (instrs @ [sil_call]) (Exp.Var id))
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
  | #SubtypeIndication.t ->
      unimplemented "trans_bounds for %s" (AdaNode.short_image bounds_expr)


(** Translate a RangeSpec which is a constraint of the form
 * "range X .. Y" to a prune node using the given expr which is expected to be
 * a rvalue *)
and trans_range_constraint ctx lal_range typ loc expr =
  let range = RangeSpec.f_range lal_range in
  match range with
  | `BoxExpr _ ->
      (* A box expr is a placeholder, it doesn't add any contraint *)
      []
  | _ ->
      let bounds_stmts, bounds_instrs, low_bound, high_bound =
        trans_bounds_ ctx (range :> [Expr.t | SubtypeIndication.t])
      in
      let bounds_constraint simple_expr =
        let instrs, exp = to_exp simple_expr in
        let prune_node =
          Sil.Prune
            ( Exp.BinOp (Binop.LAnd, Exp.le low_bound exp, Exp.le exp high_bound)
            , loc
            , true
            , Sil.Ik_bexp )
        in
        [ Block
            { instrs= bounds_instrs @ instrs @ [prune_node]
            ; loc
            ; nodekind= Procdesc.Node.(Prune_node (true, Sil.Ik_bexp, PruneNodeKind_InBound)) } ]
      in
      bounds_stmts @ map_to_stmts ~f:bounds_constraint loc expr


(** Translate a constraint on discriminants to prune nodes on the given expressions.
 * The expression is assumed to be an lvalue.
 * We generate constraints by accessing each discriminant that have a constraint
 * and prune the contraint with the expression in the AssocList *)
and trans_discriminant_constraint ctx lal_discr typ loc expr =
  let params_actual =
    DiscriminantConstraint.f_constraints lal_discr |> AssocList.p_zip_with_params
  in
  let constrain_discriminant {ParamActual.param; actual} =
    let actual_stmts, actual_expr = trans_expr_ ctx Inline actual in
    let mk_equal lhs_exp rhs_exp =
      (* TODO: access to the field name is temporary, waiting a lal fix for param actual *)
      let access_field =
        Exp.Lfield (lhs_exp, Option.value_exn (AdaNode.p_xref param) |> field_name, typ)
      in
      let load_instrs, load_exp = load typ loc access_field in
      (load_instrs, Exp.eq load_exp rhs_exp)
    in
    let mk_prune_node simple_expr =
      let instrs, exp = to_exp simple_expr in
      let prune_node = Sil.Prune (exp, loc, true, Sil.Ik_bexp) in
      [ Block
          { instrs= instrs @ [prune_node]
          ; loc
          ; nodekind= Procdesc.Node.(Prune_node (true, Sil.Ik_bexp, PruneNodeKind_InBound)) } ]
    in
    actual_stmts @ (combine ~f:mk_equal expr actual_expr |> map_to_stmts ~f:mk_prune_node loc)
  in
  List.map ~f:constrain_discriminant params_actual |> List.concat


(* Compute the first and the last expression for the array bounds *)
and trans_array_constraints_bounds ctx constraints =
  (* given a list of constraints, return the bounds *)
  match (constraints :> AdaNode.t list) with
  | [((#Expr.t | #SubtypeIndication.t) as constr)] ->
      trans_bounds_ ctx constr
  | [(_ as constr)] ->
      unimplemented "trans_constraints_bounds for %s" (AdaNode.short_image constr)
  | _ ->
      unimplemented "trans_constraints_bounds for multi-dimentional arrays"


(** Translate a constraint on index to prune nodes on the given expressions.
 * The expression is assumed to be an lvalue of an array *)
and trans_array_constraints ctx constraints typ loc expr =
  let int_typ = Typ.(mk (Tint IInt)) in
  let bounds_stmts, bounds_instrs, first, last = trans_array_constraints_bounds ctx constraints in
  let f simple_expr =
    let expr_instrs, exp = to_exp simple_expr in
    let first_field = mk_array_access ctx typ loc exp First in
    let load_first_instrs, loaded_first = load int_typ loc first_field in
    let last_field = mk_array_access ctx typ loc exp Last in
    let load_last_instrs, loaded_last = load int_typ loc last_field in
    let length_field = mk_array_access ctx typ loc exp Length in
    let load_length_instrs, loaded_length = load int_typ loc length_field in
    let prune_length simple_expr =
      let length_instrs, length_exp = to_exp simple_expr in
      [ Block
          { instrs=
              length_instrs @ load_length_instrs
              @ [Sil.Prune (Exp.eq length_exp loaded_length, loc, true, Sil.Ik_bexp)]
          ; loc
          ; nodekind=
              Procdesc.Node.Prune_node (true, Sil.Ik_bexp, Procdesc.Node.PruneNodeKind_InBound) }
      ]
    in
    let prune_length_stmts =
      (* To compute the length of the array, we use an if expression:
       * if first <= last then last - first + 1 else 0 *)
      map_to_stmts ~f:prune_length loc
        (If
           ( bounds_instrs
           , Exp.le first last
           , ( of_exp bounds_instrs
                 (Exp.BinOp
                    ( Binop.PlusA (Some Typ.IInt)
                    , Exp.BinOp (Binop.MinusA (Some Typ.IInt), last, first)
                    , Exp.one ))
             , of_exp [] Exp.zero ) ))
    in
    let instrs =
      bounds_instrs @ expr_instrs @ load_first_instrs @ load_last_instrs @ load_length_instrs
      @ [ Sil.Prune (Exp.eq loaded_first first, loc, true, Sil.Ik_bexp)
        ; Sil.Prune (Exp.eq loaded_last last, loc, true, Sil.Ik_bexp)
        ; Sil.Prune (Exp.le Exp.zero loaded_length, loc, true, Sil.Ik_bexp) ]
    in
    prune_length_stmts
    @ [ Block
          { instrs
          ; loc
          ; nodekind= Procdesc.Node.(Prune_node (true, Sil.Ik_bexp, PruneNodeKind_InBound)) } ]
  in
  bounds_stmts @ map_to_stmts ~f loc expr


(** Translate a constraint on a type to prune nodes on the given expressions.
 * The expression is assumed to be an lvalue *)
and trans_constraint ctx lal_constraint typ loc expr =
  match (lal_constraint : Constraint.t) with
  | `RangeConstraint {f_range= (lazy range)} ->
      trans_range_constraint ctx range typ loc (mk_load typ loc expr)
  | `DiscriminantConstraint _ as discr ->
      trans_discriminant_constraint ctx discr typ loc expr
  | `IndexConstraint {f_constraints= (lazy (`ConstraintList {list= (lazy constraints)}))} ->
      trans_array_constraints ctx constraints typ loc expr
  | `DeltaConstraint _ | `DigitsConstraint _ ->
      unimplemented "trans_constraint for %s" (AdaNode.short_image lal_constraint)


(** Translate constraints on subtype indications to prune nodes on the given expressions.
 * The expression is assumed to be an lvalue. A subtype indication is a node
 * of the form: Integer range 1 .. 10. So we first generate the constraints of
 * the base type and we append the other constraint if it has one *)
and trans_subtype_indication_constraint ctx subtype_indication typ loc expr =
  match Name.p_referenced_decl (SubtypeIndication.f_name subtype_indication) with
  | Some (#BaseTypeDecl.t as subtype_decl) ->
      let subtype_constraint_stmts = trans_type_constraint ctx subtype_decl typ loc expr in
      let constraint_stmts =
        match SubtypeIndication.f_constraint subtype_indication with
        | Some constr ->
            trans_constraint ctx constr typ loc expr
        | None ->
            []
      in
      subtype_constraint_stmts @ constraint_stmts
  | _ ->
      L.die InternalError "Cannot generate a type constraints for subtype %s"
        (AdaNode.short_image subtype_indication)


(** Translate constraints on an enum type to prune nodes on the given expressions.
 * The expression is assumed to be an rvalue.
 * For an enum type with 10 elements, we generate a constraint of the form:
 * 0 <= expr <= 9 *)
and trans_enum_type_constraint ctx enum_type typ loc expr =
  let literals = EnumTypeDef.f_enum_literals enum_type |> EnumLiteralDeclList.f_list in
  let lit_number = List.length literals in
  let mk_comp simple_expr =
    (* prune the expression 0 <= expr <= (lit_number - 1) *)
    let instrs, exp = to_exp simple_expr in
    let comp =
      Exp.BinOp
        (Binop.LAnd, Exp.le Exp.zero exp, Exp.le exp (Exp.int (IntLit.of_int (lit_number - 1))))
    in
    let prune_node = Sil.Prune (comp, loc, true, Sil.Ik_bexp) in
    [ Block
        { instrs= instrs @ [prune_node]
        ; loc
        ; nodekind= Procdesc.Node.(Prune_node (true, Sil.Ik_bexp, PruneNodeKind_InBound)) } ]
  in
  map_to_stmts ~f:mk_comp loc expr


and trans_array_type_constraints ctx array_type typ loc expr =
  let indices = ArrayTypeDef.f_indices array_type in
  match indices with
  | `ConstrainedArrayIndices {f_list= (lazy (`ConstraintList {list= (lazy constraints)}))} ->
      trans_array_constraints ctx constraints typ loc expr
  | _ ->
      unimplemented "trans_array_bounds for a %s" (AdaNode.short_image indices)


(** Generate the constraints to apply on expr for any type.
 * expr should be an lvalue *)
and trans_type_constraint ctx lal_typ typ loc expr =
  match (lal_typ :> BaseTypeDecl.t) with
  | `TypeDecl {f_type_def= (lazy (`SignedIntTypeDef {f_range= (lazy range)}))} ->
      trans_range_constraint ctx range typ loc (mk_load typ loc expr)
  | `TypeDecl
      {f_type_def= (lazy (`DerivedTypeDef {f_subtype_indication= (lazy subtype_indication)}))} ->
      trans_subtype_indication_constraint ctx subtype_indication typ loc expr
  | `TypeDecl {f_type_def= (lazy (#EnumTypeDef.t as enum_type))} ->
      trans_enum_type_constraint ctx enum_type typ loc (mk_load typ loc expr)
  | `TypeDecl {f_type_def= (lazy (#ArrayTypeDef.t as array_type))} ->
      trans_array_type_constraints ctx array_type typ loc expr
  | `TypeDecl {f_type_def= (lazy (#RecordTypeDef.t as record_type))} ->
      (* No particular constraints are applicable for a base record type *)
      []
  | _ ->
      unimplemented "trans_type_constraint for %s" (AdaNode.short_image lal_typ)


and trans_membership_expr_ : type a.
       context
    -> a continuation
    -> Typ.t
    -> Location.t
    -> expr
    -> [Expr.t | SubtypeIndication.t] list
    -> stmt list * a =
 fun ctx cont typ loc expr alternatives ->
  let trans_alternative alt =
    let choice_stmts, choice_instrs, low_bound, high_bound =
      trans_bounds_ ctx (alt :> [Expr.t | SubtypeIndication.t])
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
  return ctx cont typ loc final_stmts final_expr


and trans_expr_ : type a. context -> a continuation -> Expr.t -> stmt list * a =
 fun ctx cont expr ->
  try
    (* We try first to evaluate the expression as an integer before calling the
     * more general translation of expressions *)
    return ctx cont (type_of_expr ctx expr) (location ctx.source_file expr) []
      (of_exp [] (Exp.int (IntLit.of_int (Expr.p_eval_as_int expr))))
  with _ -> trans_any_expr_ ctx cont expr


and trans_any_expr_ : type a. context -> a continuation -> Expr.t -> stmt list * a =
 fun ctx cont expr ->
  let typ = type_of_expr ctx expr in
  let loc = location ctx.source_file expr in
  match (expr :> Expr.t) with
  | #IntLiteral.t as int_literal ->
      let value = IntLiteral.p_denoted_value int_literal in
      return ctx cont typ loc [] (of_exp [] (Exp.Const (Const.Cint (IntLit.of_int value))))
  | (#Identifier.t | #DottedName.t) as ident when Name.p_is_call ident -> (
    match Name.p_referenced_decl ident with
    | Some call_ref ->
        trans_call ctx cont ident call_ref []
    | _ ->
        unimplemented "trans_expr for an identifier call %s" (AdaNode.short_image ident) )
  | `AttributeRef {f_prefix= (lazy prefix); f_attribute= (lazy attribute)}
  | `UpdateAttributeRef {f_prefix= (lazy prefix); f_attribute= (lazy attribute)}
    when is_access attribute ->
      let dest_stmts, (dest_instrs, dest) = trans_lvalue_ ctx prefix in
      return ctx cont typ loc dest_stmts (of_exp dest_instrs dest)
  | `UnOp {f_op= (lazy op); f_expr= (lazy expr)} as unop -> (
    match Name.p_referenced_decl op with
    | Some ref ->
        trans_call ctx cont unop ref ([(Copy, expr)] :> (param_mode * Expr.t) list)
    | None ->
        trans_unop ctx cont unop )
  | #BinOp.t as binop -> (
      let lhs = BinOp.f_left binop in
      let op = BinOp.f_op binop in
      let rhs = BinOp.f_right binop in
      match Name.p_referenced_decl op with
      | Some ref ->
          trans_call ctx cont binop ref ([(Copy, lhs); (Copy, rhs)] :> (param_mode * Expr.t) list)
      | None ->
          trans_binop ctx cont binop )
  | `CallExpr {f_name= (lazy name); f_suffix= (lazy (#AssocList.t as assoc_list))} as call_expr
    when Name.p_is_call call_expr -> (
      let sorted_params =
        AssocList.p_zip_with_params assoc_list
        |> sort_params ctx.proc_desc
        |> List.map ~f:(fun {ParamActual.param; actual} ->
               match DefiningName.p_basic_decl param with
               | Some (#ParamSpec.t as param_spec) ->
                   ( param_mode (ParamSpec.f_type_expr param_spec) (ParamSpec.f_mode param_spec)
                   , actual )
               | _ ->
                   L.die InternalError "Should be called on a procedure param_actuals" )
      in
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
        trans_membership_expr_ ctx Inline typ loc tested_expr
          (alternatives :> [Expr.t | SubtypeIndication.t] list)
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
      return ctx cont typ loc (tested_stmts @ membership_stmts) inlined_expr
  | `IfExpr
      { f_cond_expr= (lazy cond_expr)
      ; f_then_expr= (lazy then_expr)
      ; f_alternatives= (lazy (`ElsifExprPartList {list= (lazy alternatives)}))
      ; f_else_expr= (lazy (Some else_expr)) } ->
      let cond_stmts, cond_expr = trans_expr_ ctx Inline (cond_expr :> Expr.t) in
      let then_stmts, then_expr = trans_expr_ ctx Inline (then_expr :> Expr.t) in
      let else_stmts, else_expr = trans_expr_ ctx Inline (else_expr :> Expr.t) in
      let f alternative (stmts, else_expr) =
        let cond_stmts, cond_expr =
          trans_expr_ ctx Inline (ElsifExprPart.f_cond_expr alternative :> Expr.t)
        in
        let then_stmts, then_expr =
          trans_expr_ ctx Inline (ElsifExprPart.f_then_expr alternative :> Expr.t)
        in
        (stmts @ then_stmts @ cond_stmts, mk_if cond_expr then_expr else_expr)
      in
      let elsif_stmts, elsif_expr =
        List.fold_right ~f ~init:(else_stmts, else_expr) alternatives
      in
      return ctx cont typ loc
        (cond_stmts @ then_stmts @ elsif_stmts)
        (mk_if cond_expr then_expr elsif_expr)
  | `ParenExpr {f_expr= (lazy expr)} ->
      trans_expr_ ctx cont (expr :> Expr.t)
  | #lvalue as lvalue ->
      let dest_stmts, (dest_instrs, dest) = trans_lvalue_ ctx lvalue in
      let load_instrs, load_exp = load typ loc dest in
      return ctx cont typ loc dest_stmts (of_exp (dest_instrs @ load_instrs) load_exp)
  | _ as expr ->
      unimplemented "trans_expr for %s" (AdaNode.short_image expr)


let trans_lvalue ctx dest = trans_lvalue_ ctx (dest :> lvalue)

let trans_expr ctx cont expr = trans_expr_ ctx cont (expr :> Expr.t)

let trans_bounds ctx bounds_expr = trans_bounds_ ctx (bounds_expr :> [Expr.t | SubtypeIndication.t])

let trans_membership_expr ctx cont typ loc expr alternatives =
  trans_membership_expr_ ctx cont typ loc expr (alternatives :> [Expr.t | SubtypeIndication.t] list)


let trans_type_expr_constraint ctx type_expr typ loc expr =
  match (type_expr :> TypeExpr.t) with
  | #SubtypeIndication.t as subtype_indication ->
      trans_subtype_indication_constraint ctx subtype_indication typ loc expr
  | _ ->
      unimplemented "trans_type_expr for %s" (AdaNode.short_image type_expr)
