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
open AdaTransExpr
open Option.Monad_infix
module L = Logging

let trans_simple_stmt ctx simple_stmt =
  let loc = location ctx.source_file simple_stmt in
  match (simple_stmt :> SimpleStmt.t) with
  | `AssignStmt {f_dest= (lazy dest); f_expr= (lazy expr)} ->
      let dest_instrs, dest_expr = trans_dest ctx dest in
      let typ = type_of_expr ctx dest in
      let f simple_expr =
        let expr_instrs, expr = to_exp simple_expr in
        let assignment = Sil.Store (dest_expr, typ, expr, loc) in
        let instrs = dest_instrs @ expr_instrs @ [assignment] in
        let nodekind = Procdesc.Node.(Stmt_node (Call "assign")) in
        [Block {instrs; loc; nodekind}]
      in
      let stmts, result = trans_expr ctx Inline expr in
      stmts @ map_to_stmts ~f ~orig_node:simple_stmt ctx result
  | `ReturnStmt {f_return_expr= (lazy (Some expr))} ->
      let typ = Procdesc.get_ret_type ctx.proc_desc in
      let f simple_expr =
        let expr_instrs, expr = to_exp simple_expr in
        let return = Exp.Lvar (Pvar.mk Ident.name_return (Procdesc.get_proc_name ctx.proc_desc)) in
        let assignment = Sil.Store (return, typ, expr, loc) in
        let instrs = expr_instrs @ [assignment] in
        let nodekind = Procdesc.Node.(Stmt_node ReturnStmt) in
        [Block {instrs; loc; nodekind}]
      in
      let stmts, result = trans_expr ctx Inline expr in
      stmts @ map_to_stmts ~f ~orig_node:simple_stmt ctx result
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
          match AdaNode.p_xref loop_name >>= fun ref -> LoopMap.find_opt ref ctx.loop_map with
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


let rec trans_if_stmt ctx orig_stmt cond_expr then_stmts else_stmts =
  let loc = location ctx.source_file orig_stmt in
  let false_label = mk_label () in
  let end_label = mk_label () in
  let stmts_expr, () = trans_expr ctx (Goto (Next, Label false_label)) cond_expr in
  let true_block = then_stmts @ [Jump (loc, Label end_label)] in
  let false_block = Label (loc, false_label) :: else_stmts in
  stmts_expr @ true_block @ false_block @ [Label (loc, end_label)]


and trans_composite_stmt ctx composite_stmt =
  match (composite_stmt :> CompositeStmt.t) with
  | #BaseLoopStmt.t as loop_stmt -> (
      let loc = location ctx.source_file composite_stmt in
      let end_loop = mk_label () in
      let new_ctx =
        match BaseLoopStmt.f_end_name loop_stmt >>= AdaNode.p_xref with
        | Some node ->
            {ctx with loop_map= LoopMap.add node end_loop ctx.loop_map; current_loop= Some end_loop}
        | None ->
            {ctx with current_loop= Some end_loop}
      in
      let loop_stmts = trans_stmts new_ctx (BaseLoopStmt.f_stmts loop_stmt) in
      match BaseLoopStmt.f_spec loop_stmt with
      | Some
          (`ForLoopSpec
            { f_iter_expr= (lazy iter_expr)
            ; f_has_reverse= (lazy has_reverse_node)
            ; f_loop_type= (lazy (`IterTypeIn _))
            ; f_var_decl= (lazy (`ForLoopVarDecl {f_id= (lazy var_id)})) }) ->
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
          let loop_var_name = unique_defining_name var_id in
          let loop_var = Pvar.mk loop_var_name (Procdesc.get_proc_name ctx.proc_desc) in
          let id = Ident.(create_fresh knormal) in
          let load_loop_var = Sil.Load (id, Exp.Lvar loop_var, typ, loc) in
          let bounds_stmts, bounds_instrs, low_bound, high_bound = trans_bounds ctx iter_expr in
          let comparison =
            if has_reverse then Exp.BinOp (Binop.Ge, Exp.Var id, low_bound)
            else Exp.BinOp (Binop.Le, Exp.Var id, high_bound)
          in
          let prune_true_block =
            Block
              { instrs=
                  bounds_instrs @ [load_loop_var; Sil.Prune (comparison, loc, true, Sil.Ik_for)]
              ; loc
              ; nodekind=
                  Procdesc.Node.Prune_node
                    (true, Sil.Ik_for, Procdesc.Node.PruneNodeKind_TrueBranch) }
          in
          let prune_false_block =
            Block
              { instrs=
                  bounds_instrs
                  @ [load_loop_var; Sil.Prune (mk_not comparison, loc, false, Sil.Ik_for)]
              ; loc= end_location ctx.source_file composite_stmt
              ; nodekind=
                  Procdesc.Node.Prune_node
                    (false, Sil.Ik_for, Procdesc.Node.PruneNodeKind_FalseBranch) }
          in
          let pre_loop_assignment =
            let rhs = if has_reverse then high_bound else low_bound in
            Block
              { instrs= bounds_instrs @ [Sil.Store (Exp.Lvar loop_var, typ, rhs, loc)]
              ; loc
              ; nodekind= Procdesc.Node.(Stmt_node (Call "assign")) }
          in
          let in_loop_assignment =
            let op = if has_reverse then Binop.MinusA None else Binop.PlusA None in
            let rhs = Exp.BinOp (op, Exp.Var id, Exp.one) in
            Block
              { instrs= [load_loop_var; Sil.Store (Exp.Lvar loop_var, typ, rhs, loc)]
              ; loc
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
      | Some (`ForLoopSpec {f_loop_type= (lazy (`IterTypeOf _))}) ->
          unimplemented "for X of ..."
      | Some (`WhileLoopSpec {f_expr= (lazy expr)}) ->
          let stmts, () = trans_expr ctx (Goto (Next, Label end_loop)) expr in
          [LoopStmt (loc, stmts @ loop_stmts, end_loop)]
      | None ->
          [LoopStmt (loc, loop_stmts, end_loop)] )
  | `NamedStmt {f_stmt= (lazy stmt)} ->
      trans_stmt ctx (stmt :> Stmt.t)
  | `IfStmt
      { IfStmtType.f_cond_expr= (lazy cond_expr)
      ; f_then_stmts= (lazy then_stmts)
      ; f_alternatives= (lazy (`ElsifStmtPartList {list= (lazy alternatives)}))
      ; f_else_stmts= (lazy else_stmts) } ->
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
      let stmts = trans_stmts ctx (HandledStmts.f_stmts handled_stmts) in
      let decl_stmts =
        match block_stmt with
        | `DeclBlock {f_decls= (lazy decl_part)} ->
            trans_decls ctx decl_part
        | `BeginBlock _ ->
            []
      in
      decl_stmts @ stmts
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
  | _ as stmt ->
      unimplemented "trans_stmt for %s" (AdaNode.short_image stmt)


and trans_decls ctx declarative_part =
  let trans_decl decl =
    match decl with
    | `ObjectDecl
        { ObjectDeclType.f_ids= (lazy (`DefiningNameList {list= (lazy names)}))
        ; f_type_expr= (lazy type_expr)
        ; f_default_expr= (lazy (Some default_expr)) } ->
        let typ = trans_type_expr ctx.tenv type_expr in
        let loc = location ctx.source_file decl in
        let assign_ids simple_expr =
          let instrs, expr = to_exp simple_expr in
          let f id =
            let name = unique_defining_name id in
            let pvar = Pvar.mk name (Procdesc.get_proc_name ctx.proc_desc) in
            Sil.Store (Lvar pvar, typ, expr, loc)
          in
          [ Block
              { instrs= instrs @ List.map ~f names
              ; loc
              ; nodekind= Procdesc.Node.(Stmt_node DeclStmt) } ]
        in
        let stmts, expr = trans_expr ctx Inline default_expr in
        stmts @ map_to_stmts ~f:assign_ids ~orig_node:declarative_part ctx expr
    | _ ->
        []
  in
  DeclarativePart.f_decls declarative_part
  |> AdaNodeList.f_list |> List.map ~f:trans_decl |> List.concat
