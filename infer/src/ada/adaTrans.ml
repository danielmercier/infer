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
open AdaTransStmt
open AdaCfg
open Option.Monad_infix
module L = Logging

(** Translate a subprogram spec to an infer procedure description, and return
 * a newly created context *)
let trans_spec cfg tenvs source_file subp_body =
  let proc_name = get_proc_name subp_body in
  let subp_spec = BaseSubpBody.f_subp_spec subp_body in
  let formals =
    SubpSpec.f_subp_params subp_spec
    >>| map_params ~f:(fun (name, typ, mode) ->
            ( unique_defining_name name
            , let ir_typ = infer_typ_of_type_expr tenvs typ in
              match param_mode typ mode with
              | Copy ->
                  ir_typ
              | Reference ->
                  (* If the variable is passed by reference, the type is a
                   * pointer to the real type *)
                  Typ.mk (Tptr (ir_typ, Pk_reference)) ) )
    |> Option.value ~default:[]
  in
  let params_modes =
    (* Create the table that maps a defining name to it's mode *)
    SubpSpec.f_subp_params subp_spec
    >>| map_params ~f:(fun (name, typ, mode) -> (name, param_mode typ mode))
    >>| List.fold_left
          ~f:(fun name_map (name, mode) -> DefiningNameMap.add name mode name_map)
          ~init:DefiningNameMap.empty
    |> Option.value ~default:DefiningNameMap.empty
  in
  let ret_type_expr = SubpSpec.f_subp_returns subp_spec in
  let ret_type =
    ret_type_expr >>| infer_typ_of_type_expr tenvs |> Option.value ~default:Typ.void
  in
  let proc_attributes =
    { (ProcAttributes.default source_file proc_name) with
      formals
    ; is_defined= true
    ; loc= location source_file subp_body
    ; ret_type }
  in
  let proc_desc = Cfg.create_proc_desc cfg proc_attributes in
  mk_context cfg tenvs source_file proc_desc params_modes ret_type_expr


(** Translate a subprogram body into a list of statements.
 *
 * The subprogram body is composed of a declaration list and a list of
 * statements
 *
 * Also create nodes for the start and the end of the procedure *)
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


(** Translate a subprogram into a list of statements by first create the
 * context for the translation of this subprogram, and then calling the
 * right function for the translation of the actual subprogram type *)
let trans_subp cfg tenvs source_file subp =
  let ctx = trans_spec cfg tenvs source_file subp in
  match (subp :> BaseSubpBody.t) with
  | `SubpBody _ as subp_body ->
      trans_subp_body ctx subp_body
  | _ ->
      unimplemented "trans_subp for %s" (AdaNode.short_image subp)


(** Translate all the subprograms in the given file.
 * This is imperative, the capture is stored in disk *)
let trans_file lal_ctx cfg tenvs source_filename =
  let source_file = SourceFile.create source_filename in
  let unit = AnalysisContext.get_from_file lal_ctx source_filename in
  match AnalysisUnit.root unit with
  | Some root ->
      let f = function
        | #BaseSubpBody.t as subp ->
            trans_subp cfg tenvs source_file subp
        | _ ->
            ()
      in
      (* Iterate over all nodes to find the subprograms *)
      AdaNode.iter f root ;
      (* When done with the translation of the subprograms, register them *)
      SourceFiles.add source_file cfg (Tenv.FileLocal tenvs.infer_tenv) None
  | None ->
      L.die InternalError "No root node for source file: %s" source_filename


let translate lal_ctx source_files =
  let cfg = Cfg.create () in
  let tenvs = {infer_tenv= Tenv.create (); ada_tenv= AdaType.create ()} in
  List.iter ~f:(trans_file lal_ctx cfg tenvs) source_files
