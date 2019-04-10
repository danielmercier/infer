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
      [Jump Exit]
  | `NullStmt _ ->
      []
  | _ ->
      unimplemented "trans_simple_stmt for %s" (AdaNode.short_image simple_stmt)


let rec trans_if_stmt ctx orig_stmt cond_expr then_stmts else_stmts =
  let false_label = mk_label () in
  let end_label = mk_label () in
  let stmts_expr, () = trans_expr ctx (Goto (Next, Label false_label)) cond_expr in
  let true_block = then_stmts @ [Jump (Label end_label)] in
  let false_block = Label false_label :: else_stmts in
  stmts_expr @ true_block @ false_block @ [Label end_label]


and trans_composite_stmt ctx composite_stmt =
  match (composite_stmt :> CompositeStmt.t) with
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
