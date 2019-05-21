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
open AdaTransExpr
open AdaType
open Option.Monad_infix
module L = Logging

(** Translate an assignment to a list of statements *)
let trans_assignment ctx orig_node precise_typ dest_instrs dest_expr expr =
  let typ = to_infer_typ ctx.tenvs.ada_tenv ctx.tenvs.infer_tenv precise_typ in
  let loc = location ctx.source_file orig_node in
  let f simple_expr =
    let expr_instrs, exp = to_exp simple_expr in
    let assignment = Sil.Store (dest_expr, typ, exp, loc) in
    let instrs = dest_instrs @ expr_instrs @ [assignment] in
    let nodekind = Procdesc.Node.(Stmt_node (Call "assign")) in
    let range_check_stmts =
      match precise_typ with
      | Discrete discrete ->
          let load_instrs, loaded = load typ loc dest_expr in
          range_check ctx loc discrete (dest_instrs @ load_instrs) loaded
      | _ ->
          []
    in
    Block {instrs; loc; nodekind} :: range_check_stmts
  in
  map_to_stmts ~f loc expr


(** Translate the libadalang statements called "SimpleStmt" *)
let trans_simple_stmt ctx simple_stmt =
  let loc = location ctx.source_file simple_stmt in
  match (simple_stmt :> SimpleStmt.t) with
  | `AssignStmt {f_dest= (lazy dest); f_expr= (lazy expr)} ->
      let precise_typ = trans_type_of_expr ctx.tenvs.ada_tenv dest in
      let dest_stmts, (dest_instrs, dest_expr) = trans_lvalue ctx dest in
      let stmts, result = trans_expr ctx Inline expr in
      dest_stmts @ stmts
      @ trans_assignment ctx simple_stmt precise_typ dest_instrs dest_expr result
  | `ReturnStmt {f_return_expr= (lazy (Some expr))} -> (
    match ctx.ret_type with
    | Some type_expr ->
        let return = Exp.Lvar (Pvar.mk Ident.name_return (Procdesc.get_proc_name ctx.proc_desc)) in
        let stmts, result = trans_expr ctx Inline expr in
        stmts
        @ trans_assignment ctx simple_stmt
            (trans_type_expr ctx.tenvs.ada_tenv type_expr)
            [] return result
    | None ->
        L.die InternalError "The function should have a return type" )
  | `ReturnStmt {f_return_expr= (lazy None)} ->
      [Jump (loc, Exit)]
  | `NullStmt _ ->
      []
  | `CallStmt {f_call= (lazy call)} ->
      let stmts, (instrs, _) = trans_expr ctx (Tmp "call") call in
      stmts @ [Block {instrs; loc; nodekind= Procdesc.Node.(Stmt_node (Call (AdaNode.text call)))}]
  | `ExitStmt {f_loop_name= (lazy loop_name_opt); f_cond_expr= (lazy cond_expr)} -> (
      let label =
        match loop_name_opt with
        | Some loop_name -> (
          match
            AdaNode.p_xref loop_name >>= fun ref -> DefiningNameMap.find_opt ref ctx.loop_map
          with
          | Some label ->
              label
          | None ->
              L.die InternalError "Cannot exit loop name %s" (AdaNode.short_image loop_name) )
        | None -> (
          match ctx.current_loop with
          | Some label ->
              label
          | None ->
              L.die InternalError "Exit stmt not inside a loop" )
      in
      match cond_expr with
      | Some expr ->
          (* We exit only if the condition is true *)
          let stmts, () = trans_expr ctx (Goto (Label label, Next)) expr in
          stmts
      | None ->
          [Jump (loc, Label label)] )
  | `Label {f_decl= (lazy (`LabelDecl {f_name= (lazy name)}))} ->
      [Label (loc, find_or_add ctx name)]
  | `GotoStmt {f_label_name= (lazy name)} ->
      let name_ref = Option.value_exn (AdaNode.p_xref name) in
      [Jump (loc, Label (find_or_add ctx name_ref))]
  | _ ->
      unimplemented "trans_simple_stmt for %s" (AdaNode.short_image simple_stmt)


(** Given an expression for the guard and statements for the then branch and
 * the else branch, construct an if statement *)
let rec trans_if_stmt ctx orig_stmt cond_expr then_stmts else_stmts =
  let loc = location ctx.source_file orig_stmt in
  let false_label = mk_label () in
  let end_label = mk_label () in
  let stmts_expr, () = trans_expr ctx (Goto (Next, Label false_label)) cond_expr in
  let true_block = then_stmts @ [Jump (loc, Label end_label)] in
  let false_block = Label (loc, false_label) :: else_stmts in
  stmts_expr @ true_block @ false_block @ [Label (loc, end_label)]


(** Translate a for loop to a list of statements.
 * We translate a for loop by setting the initial value of the loop variable
 * and incrementing it by one at each iteration.
 *
 * Note that in case of static predicates, the behaviour is wrong since
 * you can have the type:
 * type Number is (One, Two, Three);
 *
 * and the subtype:
 * subtype OneThree is Number with Predicate => OneThree /= Two.
 *
 * In which case doing:
 * for E in OneThree
 *
 * Should iterate on One and Three but not Two.
 *
 * One solution for this problem would be to add at the beginning of the loop:
 * if Predicate (E) then
 *    ...
 * end if
 *
 * *)
and trans_for_loop ctx composite_stmt end_loop for_loop_spec loop_stmts =
  match (for_loop_spec :> ForLoopSpec.t) with
  | `ForLoopSpec
      { f_iter_expr= (lazy iter_expr)
      ; f_has_reverse= (lazy has_reverse_node)
      ; f_loop_type= (lazy (`IterTypeIn _))
      ; f_var_decl= (lazy (`ForLoopVarDecl {f_id= (lazy var_id)})) } ->
      let typ =
        (* DiscreteSubtypeIndication is not an expr, so we need to filter
             * the different possible values of iter_expr, to return the IR type *)
        match iter_expr with
        | ( `CharLiteral _
          | `RelationOp _
          | `ExplicitDeref _
          | `StringLiteral _
          | `AttributeRef _
          | `CallExpr _
          | `TargetName _
          | `BinOp _
          | `QualExpr _
          | `DottedName _
          | `UpdateAttributeRef _
          | `Identifier _ ) as expr ->
            type_of_expr ctx expr
        | `DiscreteSubtypeIndication {f_name= (lazy name)} ->
            type_of_expr ctx name
      in
      let has_reverse = ReverseNode.p_as_bool has_reverse_node in
      let loop_var = pvar ctx var_id in
      let id = Ident.(create_fresh knormal) in
      let load_loop_var = Sil.Load (id, Exp.Lvar loop_var, typ, location ctx.source_file var_id) in
      let bounds_stmts, bounds_instrs, low_bound, high_bound = trans_bounds ctx iter_expr in
      let comparison =
        if has_reverse then Exp.BinOp (Binop.Ge, Exp.Var id, low_bound)
        else Exp.BinOp (Binop.Le, Exp.Var id, high_bound)
      in
      let loc = location ctx.source_file composite_stmt in
      let end_loc = end_location ctx.source_file composite_stmt in
      (* block to enter inside the loop *)
      let prune_true_block =
        Block
          { instrs= bounds_instrs @ [load_loop_var; Sil.Prune (comparison, loc, true, Sil.Ik_for)]
          ; loc
          ; nodekind=
              Procdesc.Node.Prune_node (true, Sil.Ik_for, Procdesc.Node.PruneNodeKind_TrueBranch)
          }
      in
      (* block to exit the loop *)
      let prune_false_block =
        Block
          { instrs=
              bounds_instrs @ [load_loop_var; Sil.Prune (mk_not comparison, loc, false, Sil.Ik_for)]
          ; loc= end_loc
          ; nodekind=
              Procdesc.Node.Prune_node (false, Sil.Ik_for, Procdesc.Node.PruneNodeKind_FalseBranch)
          }
      in
      (* The assignment of the loop variable to the first (or last) value *)
      let pre_loop_assignment =
        let rhs = if has_reverse then high_bound else low_bound in
        Block
          { instrs= bounds_instrs @ [Sil.Store (Exp.Lvar loop_var, typ, rhs, loc)]
          ; loc
          ; nodekind= Procdesc.Node.(Stmt_node (Call "assign")) }
      in
      (* The incremente (or decrement) of the loop variable *)
      let in_loop_assignment =
        let op =
          if has_reverse then Binop.MinusA (Some Typ.IInt) else Binop.PlusA (Some Typ.IInt)
        in
        let rhs = Exp.BinOp (op, Exp.Var id, Exp.one) in
        Block
          { instrs= [load_loop_var; Sil.Store (Exp.Lvar loop_var, typ, rhs, loc)]
          ; loc= end_loc
          ; nodekind= Procdesc.Node.(Stmt_node (Call "assign")) }
      in
      [ pre_loop_assignment
      ; LoopStmt
          ( loc
          , bounds_stmts
            @ [ Split
                  ( loc
                  , [ [prune_true_block] @ loop_stmts @ [in_loop_assignment]
                    ; [prune_false_block] @ [Jump (loc, Label end_loop)] ] ) ]
          , end_loop ) ]
  | `ForLoopSpec {f_loop_type= (lazy (`IterTypeOf _))} ->
      unimplemented "for X of ..."


(** Translate the libadalang statements called "CompositeStmt" *)
and trans_composite_stmt ctx composite_stmt =
  match (composite_stmt :> CompositeStmt.t) with
  | #BaseLoopStmt.t as loop_stmt -> (
      let loc = location ctx.source_file composite_stmt in
      let end_loop = mk_label () in
      let new_ctx =
        (* Insert the loop that we are in and the name of the exit label for
         * this loop in a new context that should be passed to translate
         * the core loop statements *)
        match BaseLoopStmt.f_end_name loop_stmt >>= AdaNode.p_xref with
        | Some node ->
            { ctx with
              loop_map= DefiningNameMap.add node end_loop ctx.loop_map
            ; current_loop= Some end_loop }
        | None ->
            {ctx with current_loop= Some end_loop}
      in
      let loop_stmts = trans_stmts new_ctx (BaseLoopStmt.f_stmts loop_stmt) in
      match BaseLoopStmt.f_spec loop_stmt with
      | Some (`ForLoopSpec _ as for_loop_spec) ->
          (* Call the previous defined function to translate a for loop *)
          trans_for_loop ctx composite_stmt end_loop for_loop_spec loop_stmts
      | Some (`WhileLoopSpec {f_expr= (lazy expr)}) ->
          (* For a while loop we translate the condition expression by either
           * going to the next instruction which is the core of the loop, or
           * the end of the loop *)
          let stmts, () = trans_expr ctx (Goto (Next, Label end_loop)) expr in
          [LoopStmt (loc, stmts @ loop_stmts, end_loop)]
      | None ->
          (* No condition to exit the loop *)
          [LoopStmt (loc, loop_stmts, end_loop)] )
  | `NamedStmt {f_stmt= (lazy stmt)} ->
      (* A named statement is a statement with a name. We don't care about it's
       * name *)
      trans_stmt ctx (stmt :> Stmt.t)
  | `IfStmt
      { IfStmtType.f_cond_expr= (lazy cond_expr)
      ; f_then_stmts= (lazy then_stmts)
      ; f_alternatives= (lazy (`ElsifStmtPartList {list= (lazy alternatives)}))
      ; f_else_stmts= (lazy else_stmts) } ->
      (* An if statement in Ada have some alternatives, but translate this like
       * if A then S1 elsif B then S2 else S3
       * to:
       *  if A then S1 else {if B then S2 else S3}
       *)
      let rec aux = function
        | alternative :: q ->
            let alt_cond_expr = ElsifStmtPart.f_cond_expr alternative in
            let alt_stmts = ElsifStmtPart.f_stmts alternative |> trans_stmts ctx in
            let else_stmts = aux q in
            trans_if_stmt ctx (alternative :> AdaNode.t) alt_cond_expr alt_stmts else_stmts
        | [] ->
            else_stmts >>| trans_stmts ctx |> Option.value ~default:[]
      in
      let trans_then_stmts = trans_stmts ctx then_stmts in
      trans_if_stmt ctx (composite_stmt :> AdaNode.t) cond_expr trans_then_stmts (aux alternatives)
  | (`BeginBlock {f_stmts= (lazy handled_stmts)} | `DeclBlock {f_stmts= (lazy handled_stmts)}) as
    block_stmt ->
      (* We translate the statements inside the block *)
      let stmts = trans_stmts ctx (HandledStmts.f_stmts handled_stmts) in
      let decl_stmts =
        (* If the block is a declarative block, we need to translate the declarations *)
        match block_stmt with
        | `DeclBlock {f_decls= (lazy decl_part)} ->
            trans_decls ctx decl_part
        | `BeginBlock _ ->
            []
      in
      decl_stmts @ stmts
  | `ExtendedReturnStmt {f_decl= (lazy decl); f_stmts= (lazy handled_stmts)} ->
      (* An extended return statement is a statement that defines a variable
       * that will then be returned.
       *
       * This is translated by adding in the subst map inside the context, the
       * fact that the defined variable is the return variable.
       *
       * Infer IR does not define a return statement, but instead, there is a
       * variable called return that is actually the returned variable *)
      let return_var = Pvar.mk Ident.name_return (Procdesc.get_proc_name ctx.proc_desc) in
      let f acc name = {acc with subst= DefiningNameMap.add name return_var acc.subst} in
      let new_ctx =
        ExtendedReturnStmtObjectDecl.f_ids decl
        |> DefiningNameList.f_list |> List.fold_left ~f ~init:ctx
      in
      let decl_stmts = trans_decl new_ctx (decl :> AdaNode.t) in
      let stmts =
        handled_stmts >>| HandledStmts.f_stmts >>| trans_stmts new_ctx |> Option.value ~default:[]
      in
      let end_stmt_loc = end_location ctx.source_file composite_stmt in
      decl_stmts @ stmts @ [Jump (end_stmt_loc, Exit)]
  | `CaseStmt
      { f_expr= (lazy expr)
      ; f_alternatives= (lazy (`CaseStmtAlternativeList {list= (lazy alternatives)})) } ->
      (* A case statement is translated into a succession of if statements.
       *
       * case X when A => S1 when B => S2 when others => S3
       *
       * is translated to:
       *
       * if X in A then S1 else {if X in B then S2 else S3}
       *
       * We use the translation of membership expression to translate the
       * conditions of the if statements
       * *)
      let loc = location ctx.source_file composite_stmt in
      let typ = type_of_expr ctx expr in
      let end_case_label = mk_label () in
      let expr_stmts, (instrs, exp) = trans_expr ctx (Tmp "case_stmt") expr in
      let is_others alt =
        match CaseStmtAlternative.f_choices alt |> AlternativesList.f_list with
        | [#OthersDesignator.t] ->
            true
        | _ ->
            false
      in
      let rec trans_alternatives = function
        | [alt] when is_others alt ->
            let case_stmts = CaseStmtAlternative.f_stmts alt |> trans_stmts ctx in
            case_stmts @ [Jump (loc, Label end_case_label)]
        | alt :: alternatives ->
            let next_case_label = mk_label () in
            let choices =
              (* Filter all choices, to be of the desired typ *)
              let f = function
                | (#Expr.t | #SubtypeIndication.t) as expr ->
                    expr
                | _ as choice ->
                    L.die InternalError "Cannot generate membership expression for %s"
                      (AdaNode.short_image choice)
              in
              CaseStmtAlternative.f_choices alt |> AlternativesList.f_list |> List.map ~f
            in
            let case_stmts = CaseStmtAlternative.f_stmts alt |> trans_stmts ctx in
            let choices_stmts, () =
              trans_membership_expr ctx
                (Goto (Next, Label next_case_label))
                typ loc (of_exp instrs exp) choices
            in
            choices_stmts @ case_stmts
            @ [Jump (loc, Label end_case_label)]
            @ [Label (loc, next_case_label)]
            @ trans_alternatives alternatives
        | [] ->
            []
      in
      expr_stmts @ trans_alternatives alternatives @ [Label (loc, end_case_label)]
  | _ ->
      unimplemented "trans_composite_stmt for %s" (AdaNode.short_image composite_stmt)


and trans_stmts ctx stmt_list =
  let trans_stmt node =
    match node with
    | #Stmt.t as stmt ->
        trans_stmt ctx stmt
    | _ ->
        unimplemented "trans_stmt from trans_stmts for %s" (AdaNode.short_image node)
  in
  StmtList.f_list stmt_list |> List.map ~f:trans_stmt |> List.concat


and trans_stmt ctx stmt =
  match (stmt :> Stmt.t) with
  | #SimpleStmt.t as simple_stmt ->
      trans_simple_stmt ctx simple_stmt
  | #CompositeStmt.t as composite_stmt ->
      trans_composite_stmt ctx composite_stmt
  | #ErrorStmt.t ->
      (* Syntax error, simply skip the statement *)
      []


and trans_array_decl ctx decl names typ indices =
  (* When an array is declared in Ada, there is an implicit allocation.
   * Translate this to a malloc call *)
  let loc = location ctx.source_file decl in
  let index_stmts, index_instrs, index_first, index_last =
    match indices with
    | [(_, index_typ)] ->
        trans_bounds_from_discrete ctx index_typ
    | _ ->
        unimplemented "multidimensional array"
  in
  let f name =
    let pvar = pvar ctx name in
    let first_typ, first_field = mk_array_access ctx typ (Exp.Lvar pvar) First in
    let last_typ, last_field = mk_array_access ctx typ (Exp.Lvar pvar) Last in
    let length_typ, length_field = mk_array_access ctx typ (Exp.Lvar pvar) Length in
    let data_typ, data_field = mk_array_access ctx typ (Exp.Lvar pvar) Data in
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
    let stores_stmts =
      index_stmts @ length_stmts
      @ [ Block
            { instrs=
                index_instrs
                @ [ Sil.Store (first_field, first_typ, index_first, loc)
                  ; Sil.Store (last_field, last_typ, index_last, loc) ]
            ; loc
            ; nodekind= Procdesc.Node.Stmt_node (Call "assign") } ]
    in
    let id = Ident.(create_fresh knormal) in
    let load_length = Sil.Load (id, length_field, length_typ, loc) in
    (* Call a malloc to allocate some space for the array.
     * TODO: Instead of calling malloc, we should call our own builtin for array
     *       declaration *)
    let malloc_res = Ident.(create_fresh knormal) in
    let allocate =
      Sil.Call
        ( (malloc_res, typ)
        , Exp.Const (Const.Cfun BuiltinDecl.malloc)
        , [(Exp.Var id, length_typ)]
        , loc
        , CallFlags.default )
    in
    let store_malloc_result = Sil.Store (data_field, data_typ, Exp.Var malloc_res, loc) in
    stores_stmts
    @ [ Block
          { instrs= [load_length; allocate; store_malloc_result]
          ; loc
          ; nodekind= Procdesc.Node.Stmt_node (Call "malloc") } ]
  in
  List.concat_map ~f names


and trans_decl ctx decl =
  match (decl :> AdaNode.t) with
  | `ObjectDecl
      { f_ids= (lazy (`DefiningNameList {list= (lazy names)}))
      ; f_type_expr= (lazy type_expr)
      ; f_default_expr= (lazy default_expr) }
  | `ExtendedReturnStmtObjectDecl
      { f_ids= (lazy (`DefiningNameList {list= (lazy names)}))
      ; f_type_expr= (lazy type_expr)
      ; f_default_expr= (lazy default_expr) } ->
      let ada_typ = trans_type_expr ctx.tenvs.ada_tenv type_expr in
      let typ = to_infer_typ ctx.tenvs.ada_tenv ctx.tenvs.infer_tenv ada_typ in
      let array_decl_stmts =
        match ada_typ with
        | Array (_, indices, _) ->
            trans_array_decl ctx decl names typ indices
        | _ ->
            []
      in
      let store_default_stmts =
        (* Check if there is a default expression and store it if there is one *)
        match default_expr with
        | Some default_expr ->
            let stmts, expr = trans_expr ctx Inline default_expr in
            let f id =
              let pvar = pvar ctx id in
              trans_assignment ctx decl ada_typ [] (Exp.Lvar pvar) expr
            in
            stmts @ List.concat_map ~f names
        | None ->
            []
      in
      array_decl_stmts @ store_default_stmts
  | _ ->
      []


and trans_decls ctx declarative_part =
  DeclarativePart.f_decls declarative_part
  |> AdaNodeList.f_list
  |> List.map ~f:(trans_decl ctx)
  |> List.concat
