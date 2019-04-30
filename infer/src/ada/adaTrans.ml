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
open AdaTransStmt
open AdaCfg
open Option.Monad_infix
module L = Logging

(** Translate a subprogram spec to an infer procedure description *)
let trans_spec cfg tenv source_file subp_body =
  let proc_name = get_proc_name subp_body in
  let subp_spec = BaseSubpBody.f_subp_spec subp_body in
  let formals =
    SubpSpec.f_subp_params subp_spec
    >>| map_params ~f:(fun (name, typ) -> (unique_defining_name name, trans_type_expr tenv typ))
    |> Option.value ~default:[]
  in
  let ret_type =
    SubpSpec.f_subp_returns subp_spec >>| trans_type_expr tenv |> Option.value ~default:Typ.void
  in
  let proc_attributes =
    { (ProcAttributes.default source_file proc_name) with
      formals
    ; is_defined= true
    ; loc= location source_file subp_body
    ; ret_type }
  in
  Cfg.create_proc_desc cfg proc_attributes


let trans_subp_body ctx subp =
  let decl_stmts = SubpBody.f_decls subp |> trans_decls ctx in
  let handled_stmts = SubpBody.f_stmts subp |> HandledStmts.f_stmts |> trans_stmts ctx in
  let start_loc = location ctx.source_file subp in
  let end_loc = end_location ctx.source_file subp in
  let start_node = Procdesc.create_node ctx.proc_desc start_loc Procdesc.Node.Start_node [] in
  let exit_node = Procdesc.create_node ctx.proc_desc end_loc Procdesc.Node.Exit_node [] in
  Procdesc.set_start_node ctx.proc_desc start_node ;
  Procdesc.set_exit_node ctx.proc_desc exit_node ;
  trans_cfg ctx (decl_stmts @ handled_stmts)


let trans_subp cfg tenv source_file subp =
  let proc_desc = trans_spec cfg tenv source_file subp in
  let ctx = mk_context cfg tenv source_file proc_desc in
  match (subp :> BaseSubpBody.t) with
  | `SubpBody _ as subp_body ->
      trans_subp_body ctx subp_body
  | _ ->
      unimplemented "trans_subp for %s" (AdaNode.short_image subp)


let trans_file lal_ctx cfg tenv source_filename =
  let source_file = SourceFile.create source_filename in
  let unit = AnalysisContext.get_from_file lal_ctx source_filename in
  match AnalysisUnit.root unit with
  | Some root ->
      let f = function
        | #BaseSubpBody.t as subp ->
            trans_subp cfg tenv source_file subp
        | _ ->
            ()
      in
      AdaNode.iter f root ;
      SourceFiles.add source_file cfg (Tenv.FileLocal tenv) None
  | None ->
      L.die InternalError "No root node for source file: %s" source_filename


let translate lal_ctx source_files =
  let cfg = Cfg.create () in
  let tenv = Tenv.create () in
  List.iter ~f:(trans_file lal_ctx cfg tenv) source_files
