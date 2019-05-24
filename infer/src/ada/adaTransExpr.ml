(*
 * Copyright (c) 2017-present, AdaCore.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 *)

open! IStd
open Libadalang
open AdaUtils
open LalUtils
open AdaFrontend
open AdaType
open Option.Monad_infix
module L = Logging

(** Return an expression equivalent to "not exp" but try to simplify it if
  * possible *)
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
  let ada_tenv = ctx.tenvs.ada_tenv in
  let infer_tenv = ctx.tenvs.infer_tenv in
  to_infer_typ ada_tenv infer_tenv (trans_type_of_expr ada_tenv expr)


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


(** To combine two expressions lhs and rhs, we append the rhs expression to
 * all the lhs leafs and we call f with the actual instructions and expressions *)
let combine ~f lhs_expr rhs_expr =
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


(** Create an if expression by going to the leafs of the condition expression
 * and create an If there with then_expr as the then branch and else_expr as
 * then else branch *)
let mk_if cond_expr then_expr else_expr =
  let f = function
    | Bool true ->
        then_expr
    | Bool false ->
        else_expr
    | Exp (instrs, exp) ->
        If (instrs, exp, (then_expr, else_expr))
  in
  map ~f cond_expr


(** Make a shortcircuit or from the two given expressions *)
let mk_or lhs_expr rhs_expr = mk_if lhs_expr (of_bool true) rhs_expr

(** Make a shortcircuit and from the two given expressions *)
let mk_and lhs_expr rhs_expr = mk_if lhs_expr rhs_expr (of_bool false)

(** Given an expression, load it and return the loaded expression *)
let mk_load typ loc expr =
  let f simple_expr =
    let instrs, exp = to_exp simple_expr in
    let load_instrs, load_exp = load typ loc exp in
    of_exp (instrs @ load_instrs) load_exp
  in
  map ~f expr


(* Type used to call mk_array_access to access a field of the array *)
type array_access = Data | First | Last | Length

(** An array is translated to a record with fields for first, last, length and
 * the data. This function should be use to access the fields of the record *)
let rec mk_array_access ctx array_typ prefix array_access =
  let data_field_name = Typ.Fieldname.Ada.from_string "data" in
  let field_typ field =
    let lookup = Tenv.lookup ctx.tenvs.infer_tenv in
    Typ.Struct.fld_typ ~lookup ~default:Typ.void field array_typ
  in
  match array_access with
  | Data ->
      let real_array_typ = field_typ data_field_name in
      (real_array_typ, Exp.Lfield (prefix, data_field_name, real_array_typ))
  | First ->
      let first_field = Typ.Fieldname.Ada.from_string "first" in
      let first_typ = field_typ first_field in
      (first_typ, Exp.Lfield (prefix, first_field, first_typ))
  | Last ->
      let last_field = Typ.Fieldname.Ada.from_string "last" in
      let last_typ = field_typ last_field in
      (last_typ, Exp.Lfield (prefix, last_field, last_typ))
  | Length ->
      let length_field = Typ.Fieldname.Ada.from_string "length" in
      let length_typ = field_typ length_field in
      (length_typ, Exp.Lfield (prefix, length_field, length_typ))


(** An lvalue is an expression that have some location in the memory. Translate
 * it to an expression symbolically representing this location. *)
let rec trans_lvalue_ ctx dest =
  let deref typ loc instrs exp =
    (* Insert the access check when dereferencing a value of pointer type *)
    let access_check_stmts = access_check loc instrs exp in
    let instrs, loaded = load typ loc exp in
    (access_check_stmts, (instrs, loaded))
  in
  match (dest :> lvalue) with
  | `DottedName {f_prefix= (lazy prefix)} as name when is_record_field_access name ->
      (* In this case dotted name is an access to the record with name prefix *)
      let rec aux acc_stmts instrs exp = function
        | Record record_name ->
            let field = field_name (Option.value_exn (AdaNode.p_xref name)) in
            let any_field =
              match lookup_field ctx.tenvs.ada_tenv record_name field with
              | Some (Field _ as any_field) | Some (Discriminant _ as any_field) ->
                  any_field
              | None ->
                  L.die InternalError "Cannot get the field %a" Typ.Fieldname.pp field
            in
            let ada_field_typ = field_typ any_field in
            let check_stmts =
              (* When accessing a record field, we want to check that we are
               * allowed to perform this access. First lookup the field, and if
               * is a regular field, convert all necessary conditions to
               * access the nodes to prune nodes on the accessed record *)
              match any_field with
              | Field {condition} ->
                  let loc = location ctx.source_file name in
                  let discriminant_checks =
                    List.concat_map
                      ~f:(discriminant_check ctx loc record_name instrs exp)
                      condition
                  in
                  discriminant_checks
              | Discriminant _ ->
                  (* No particular condition are applied to a discriminant field *)
                  []
            in
            let field_typ = to_infer_typ ctx.tenvs.ada_tenv ctx.tenvs.infer_tenv ada_field_typ in
            (acc_stmts @ check_stmts, (instrs, Exp.Lfield (exp, field, field_typ)))
        | Access root_typ ->
            (* Implicit dereference *)
            let typ = to_infer_typ ctx.tenvs.ada_tenv ctx.tenvs.infer_tenv root_typ in
            let access_check_stmts, (load_instrs, loaded) =
              deref typ (location ctx.source_file dest) instrs exp
            in
            aux (acc_stmts @ access_check_stmts) load_instrs loaded root_typ
        | _ ->
            L.die InternalError "Variable %s should be of record type" (AdaNode.short_image prefix)
      in
      let typ = trans_type_of_expr ctx.tenvs.ada_tenv prefix in
      let prefix_stmts, (prefix_instrs, prefix_expr) = trans_lvalue_ ctx prefix in
      aux prefix_stmts prefix_instrs prefix_expr typ
  | (`DottedName _ | `Identifier _) as name -> (
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
      let access_check_stmts, (load_instrs, load_expr) =
        deref (type_of_expr ctx prefix) (location ctx.source_file dest) instrs dest_expr
      in
      (access_check_stmts @ stmts, (instrs @ load_instrs, load_expr))
  | `CallExpr {f_name= (lazy name); f_suffix= (lazy (`AssocList {list= (lazy assoc_list)}))} ->
      let loc = location ctx.source_file name in
      let rec aux acc_stmts array_dest_instrs array_dest typ =
        match typ with
        | Array (_, _, [index_typ], _) ->
            (* Since we are evaluating an lvalue, consider this as an access to an
             * array. An array is compiled to a record with the field data being the
             * real array. *)
            let array_typ = to_infer_typ ctx.tenvs.ada_tenv ctx.tenvs.infer_tenv typ in
            let index_dest_stmts, (index_dest_instrs, index_dest) =
              match assoc_list with
              | [`ParamAssoc {f_designator= (lazy None); f_r_expr= (lazy index_expr)}] ->
                  trans_expr_ ctx (Tmp "index") (index_expr :> Expr.t)
              | _ ->
                  unimplemented
                    "trans_lvalue for a CallExpr for assoc_list other than one ParamAssoc"
            in
            let data_typ, field = mk_array_access ctx array_typ array_dest Data in
            let array_access_instrs, loaded = load data_typ loc field in
            let array_access = Exp.Lindex (loaded, index_dest) in
            let index_check_stmts =
              (* When accessing an index of an array, we want to be sure that it
               * is between first and last, this is performed by adding a this check *)
              array_index_check ctx loc index_typ index_dest_instrs index_dest
            in
            ( acc_stmts @ index_dest_stmts @ index_check_stmts
            , (array_dest_instrs @ index_dest_instrs @ array_access_instrs, array_access) )
        | Array _ ->
            unimplemented "trans_lvalue for multidimensional array"
        | Access ada_typ ->
            (* Implicit dereference *)
            let typ = to_infer_typ ctx.tenvs.ada_tenv ctx.tenvs.infer_tenv ada_typ in
            let access_check_stmts, (load_instrs, loaded) =
              deref typ (location ctx.source_file dest) array_dest_instrs array_dest
            in
            aux (acc_stmts @ access_check_stmts) load_instrs loaded ada_typ
        | _ ->
            L.die InternalError "Unexpected non array type for %s" (AdaNode.short_image dest)
      in
      let array_precise_typ = trans_type_of_expr ctx.tenvs.ada_tenv name in
      let array_dest_stmts, (array_dest_instrs, array_dest) = trans_lvalue_ ctx name in
      aux array_dest_stmts array_dest_instrs array_dest array_precise_typ
  | `CallExpr
      { f_name= (lazy name)
      ; f_suffix=
          (lazy
            ( ( `DottedName _
              | `TargetName _
              | `ExplicitDeref _
              | `AttributeRef _
              | `RelationOp _
              | `CharLiteral _
              | `QualExpr _
              | `Identifier _
              | `StringLiteral _
              | `DiscreteSubtypeIndication _
              | `UpdateAttributeRef _
              | `BinOp _
              | `CallExpr _ ) as suffix )) } ->
      let ada_typ = trans_type_of_expr ctx.tenvs.ada_tenv dest in
      trans_array_slice ctx ada_typ (location ctx.source_file dest) name
  | _ as expr ->
      unimplemented "trans_lvalue for %s" (AdaNode.short_image expr)


and trans_array_slice ctx ada_typ loc name =
  (* Array slicing is implemented by creating a temporary array and assigning
   * first and last according to the suffix, for example for
   * A (1 .. 10)
   *
   * we create a tmp A' and assign:
   * A'.first := 1
   * A'.last := 10
   * A'.data := A.data
   *
   * Thus, we create an alias between the field data of tmp and the field
   * data of the actual array *)
  let array_typ = to_infer_typ ctx.tenvs.ada_tenv ctx.tenvs.infer_tenv ada_typ in
  let array_src_stmts, (array_src_instrs, array_src) = trans_lvalue_ ctx name in
  let array_target = Pvar.mk_tmp (AdaNode.text name) (Procdesc.get_proc_name ctx.proc_desc) in
  let data_typ, data = mk_array_access ctx array_typ array_src Data in
  let load_data_instrs, loaded_data = load data_typ loc data in
  let new_array_stmts =
    mk_array ctx loc (Exp.Lvar array_target) ada_typ
      (array_src_instrs @ load_data_instrs)
      loaded_data
  in
  (array_src_stmts @ new_array_stmts, ([], Exp.Lvar array_target))


(** Translate binop operations into the Sil corresponding expression *)
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


(** Translate unary operations into the Sil corresponding expression *)
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


(** Translate an enum literal to an integer. But we don't care about the
 * representation. This means that the returned integer is not equivalent to
 * calling 'Pos in Ada *)
and trans_enum_literal : type a.
    context -> a continuation -> Typ.t -> Location.t -> EnumLiteralDecl.t -> stmt list * a =
 fun ctx cont typ loc enum_lit ->
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


(** Translate an Ada call into some stmts *)
and trans_call : type a.
       context
    -> a continuation
    -> [< Expr.t]
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


(** Get the expression from either an int or a lal expression *)
and of_int_or_lal_expr ctx = function
  | Int i ->
      ([], ([], Exp.int (IntLit.of_int i)))
  | Lal lal_expr ->
      trans_expr_ ctx (Tmp "") lal_expr


(** Translate a discrete type to expressions for lower and higher bounds *)
and trans_bounds_from_discrete ctx typ =
  let of_ada_type_expr_minus_one = function
    | Int i ->
        ([], ([], Exp.int (IntLit.of_int (i - 1))))
    | Lal lal_expr ->
        let stmts, (instrs, exp) = of_int_or_lal_expr ctx (Lal lal_expr) in
        (stmts, (instrs, Exp.BinOp (Binop.MinusA (Some Typ.IInt), exp, Exp.one)))
  in
  match typ with
  | Signed (lower, upper) ->
      let lower_stmts, (lower_instrs, lower_exp) = of_int_or_lal_expr ctx lower in
      let upper_stmts, (upper_instrs, upper_exp) = of_int_or_lal_expr ctx upper in
      (lower_stmts @ upper_stmts, lower_instrs @ upper_instrs, lower_exp, upper_exp)
  | Enum max | Mod max ->
      let stmt_upper, (upper_instrs, upper_exp) = of_ada_type_expr_minus_one max in
      (stmt_upper, upper_instrs, Exp.zero, upper_exp)


and trans_bounds_ ctx bounds_expr =
  let trans_bounds_from_type typ =
    match typ with
    | Discrete discrete ->
        trans_bounds_from_discrete ctx discrete
    | _ ->
        L.die InternalError "Cannot generate a range from a non discrete type"
  in
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
    | #lvalue as lvalue -> (
      match Name.p_referenced_decl lvalue with
      | Some (#BaseTypeDecl.t as base_type_decl) ->
          (* In this case, the lvalue refers to a type, lets translate the
           * type to bounds *)
          let typ = trans_type_decl ctx.tenvs.ada_tenv base_type_decl in
          trans_bounds_from_type typ
      | _ ->
          let stmts, (instrs, exp) = trans_expr_ ctx (Tmp "") (lvalue :> Expr.t) in
          (stmts, instrs, exp, exp) )
    | _ ->
        unimplemented "trans_bounds for %s" (AdaNode.short_image bounds_expr) )
  | #SubtypeIndication.t as subtype ->
      let typ = trans_type_expr ctx.tenvs.ada_tenv subtype in
      trans_bounds_from_type typ


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
        |> sort_params
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
  | `NullLiteral _ ->
      return ctx cont typ loc [] (of_exp [] Exp.null)
  | _ as expr ->
      unimplemented "trans_expr for %s" (AdaNode.short_image expr)


and mk_array ctx loc array_access ada_typ data_instrs data =
  let typ = to_infer_typ ctx.tenvs.ada_tenv ctx.tenvs.infer_tenv ada_typ in
  match ada_typ with
  | Array (_, _, [index_typ], _) ->
      let index_stmts, index_instrs, index_first, index_last =
        trans_bounds_from_discrete ctx index_typ
      in
      let first_typ, first_field = mk_array_access ctx typ array_access First in
      let last_typ, last_field = mk_array_access ctx typ array_access Last in
      let length_typ, length_field = mk_array_access ctx typ array_access Length in
      let data_typ, data_field = mk_array_access ctx typ array_access Data in
      let store_length simple_expr =
        let length_instrs, length_exp = to_exp simple_expr in
        [ Block
            { instrs= length_instrs @ [Sil.Store (length_field, length_typ, length_exp, loc)]
            ; loc
            ; nodekind= Procdesc.Node.Stmt_node (Call "assign") } ]
      in
      let length_stmts =
        (* To compute the length of the array, we use an if expression:
     * if first <= last then last - first + 1 else 0 *)
        map_to_stmts ~f:store_length loc
          (If
             ( index_instrs
             , Exp.le index_first index_last
             , ( of_exp index_instrs
                   (Exp.BinOp
                      ( Binop.PlusA (Some Typ.IInt)
                      , Exp.BinOp (Binop.MinusA (Some Typ.IInt), index_last, index_first)
                      , Exp.one ))
               , of_exp [] Exp.zero ) ))
      in
      index_stmts @ length_stmts
      @ [ Block
            { instrs=
                index_instrs @ data_instrs
                @ [ Sil.Store (first_field, first_typ, index_first, loc)
                  ; Sil.Store (last_field, last_typ, index_last, loc)
                  ; Sil.Store (data_field, data_typ, data, loc) ]
            ; loc
            ; nodekind= Procdesc.Node.Stmt_node (Call "assign") } ]
  | _ ->
      []


and discrete_check ctx kind loc discrete_typ instrs exp =
  let bounds_stmts, bounds_instrs, lower_exp, upper_exp =
    trans_bounds_from_discrete ctx discrete_typ
  in
  let in_between = Exp.BinOp (Binop.LAnd, Exp.le lower_exp exp, Exp.le exp upper_exp) in
  let prune = Sil.Prune (in_between, loc, true, Sil.Ik_bexp) in
  bounds_stmts
  @ [ Block
        { instrs= bounds_instrs @ instrs @ [prune]
        ; loc
        ; nodekind=
            Procdesc.Node.Prune_node (true, Sil.Ik_bexp, Procdesc.Node.PruneNodeKind_AdaCheck kind)
        } ]


and array_index_check ctx loc index_typ index_instrs index_exp =
  discrete_check ctx Procdesc.Node.IndexCheck loc index_typ index_instrs index_exp


and range_check ctx loc discrete_typ instrs exp =
  discrete_check ctx Procdesc.Node.RangeCheck loc discrete_typ instrs exp


and access_check loc instrs exp =
  let not_null = Exp.ne exp Exp.null in
  let prune = Sil.Prune (not_null, loc, true, Sil.Ik_bexp) in
  [ Block
      { instrs= instrs @ [prune]
      ; loc
      ; nodekind=
          Procdesc.Node.Prune_node
            (true, Sil.Ik_bexp, Procdesc.Node.PruneNodeKind_AdaCheck AccessCheck) } ]


and discriminant_check ctx loc record_name instrs exp (discriminant, condition) =
  let ada_field_typ =
    Option.value_exn (lookup_field ctx.tenvs.ada_tenv record_name discriminant >>| field_typ)
  in
  let field_typ = to_infer_typ ctx.tenvs.ada_tenv ctx.tenvs.infer_tenv ada_field_typ in
  let access_discr = Exp.Lfield (exp, discriminant, field_typ) in
  let load_instrs, loaded = load field_typ loc access_discr in
  let stmts, (check_instrs, check) =
    match condition with
    | Equal expr ->
        let stmts, (instrs, exp) = of_int_or_lal_expr ctx expr in
        (stmts, (instrs, Exp.eq loaded exp))
    | InRange (lower, upper) ->
        let lower_stmts, (lower_instrs, lower_exp) = of_int_or_lal_expr ctx lower in
        let upper_stmts, (upper_instrs, upper_exp) = of_int_or_lal_expr ctx upper in
        ( lower_stmts @ upper_stmts
        , ( lower_instrs @ upper_instrs
          , Exp.BinOp (Binop.LAnd, Exp.le lower_exp loaded, Exp.le loaded upper_exp) ) )
    | LessThan expr ->
        let stmts, (instrs, exp) = of_int_or_lal_expr ctx expr in
        (stmts, (instrs, Exp.lt loaded exp))
  in
  let prune = Sil.Prune (check, loc, true, Sil.Ik_bexp) in
  stmts
  @ [ Block
        { instrs= instrs @ load_instrs @ check_instrs @ [prune]
        ; loc
        ; nodekind=
            Procdesc.Node.Prune_node
              (true, Sil.Ik_bexp, Procdesc.Node.PruneNodeKind_AdaCheck DiscriminantCheck) } ]


let trans_lvalue ctx dest = trans_lvalue_ ctx (dest :> lvalue)

let trans_expr ctx cont expr = trans_expr_ ctx cont (expr :> Expr.t)

let trans_bounds ctx bounds_expr = trans_bounds_ ctx (bounds_expr :> [Expr.t | SubtypeIndication.t])

let trans_membership_expr ctx cont typ loc expr alternatives =
  trans_membership_expr_ ctx cont typ loc expr (alternatives :> [Expr.t | SubtypeIndication.t] list)
