(*
 * Copyright (c) 2017-present, AdaCore.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 *)

open! IStd
open AdaFrontend
module L = Logging

(* This type is used within this module only.
 * This is used to implement backward references of labels.
 * When we have a backward reference of a label, instead of returning Nodes,
 * we return Unknown with the backward reference label *)
type t = Nodes of Procdesc.Node.t list | Unknown of Label.t

let trans_cfg ctx stmts =
  (* Map a label to an infer node, so that we can use it for jumps *)
  let label_map = Hashtbl.create (module Label) in
  let register_label label nodes =
    (* Wrapper around Hashtbl.add that raise an error when we have a duplicate *)
    match Hashtbl.add label_map ~key:label ~data:nodes with
    | `Ok ->
        ()
    | `Duplicate ->
        L.die InternalError "Duplicate label: %a" Label.pp label
  in
  (* table that maps a node to a label. This is used for backward references,
   * whenever we cannot directly set the successors of a node because of a
   * backward reference to a label, we add the node to this table *)
  let node_table = Caml.Hashtbl.create (List.length stmts) in
  let register_node loc = function
    (* Whenever we need a node and Unknown is returned, we can call this. This
     * function creates a new node and add it to the node table so that it's
     * successors can be registered later. *)
    | Nodes nodes ->
        nodes
    | Unknown label ->
        let new_node =
          Procdesc.create_node ctx.proc_desc loc (Procdesc.Node.Skip_node "Label") []
        in
        Caml.Hashtbl.add node_table new_node label ;
        [new_node]
  in
  let procedure_start_node = Procdesc.get_start_node ctx.proc_desc in
  let procedure_exit_node = Procdesc.get_exit_node ctx.proc_desc in
  let rec trans_stmts following_nodes stmts =
    (* This function should return the node created for the first stmt of the given statemnt list.
     * If the list is empty, following_nodes is returned instead *)
    match stmts with
    | stmt :: stmts -> (
      match stmt with
      | Block block ->
          (* We create a node for a bloc, so we return it *)
          let new_node =
            Procdesc.create_node ctx.proc_desc block.loc block.nodekind block.instrs
          in
          let next_nodes = trans_stmts following_nodes stmts in
          ( match next_nodes with
          | Nodes nodes ->
              Procdesc.node_set_succs_exn ctx.proc_desc new_node nodes []
          | Unknown label ->
              (* This means that we are jumping to the given label.
               * Register new_node so successors will be set later *)
              Caml.Hashtbl.add node_table new_node label ) ;
          Nodes [new_node]
      | Label (loc, label) ->
          (* We do not create a node for a label, we simply register it to
           * point to the nodes for the following stmt *)
          let next_nodes = trans_stmts following_nodes stmts |> register_node loc in
          register_label label next_nodes ; Nodes next_nodes
      | Jump (_, jump_kind) -> (
          (* We do not create a node for a jump, thus the returned node depends
           * on where we jump to *)
          let next_nodes = trans_stmts following_nodes stmts in
          match jump_kind with
          | Next ->
              next_nodes
          | Label label -> (
            match Hashtbl.find label_map label with
            | Some nodes ->
                Nodes nodes
            | None ->
                Unknown label )
          | Exit ->
              Nodes [procedure_exit_node] )
      | Split (loc, blocks) ->
          (* We do not create a node for a split. The nodes returned are
           * the nodes returned by all the branches of the split *)
          let next_nodes = trans_stmts following_nodes stmts |> register_node loc in
          Nodes
            ( List.map ~f:(trans_stmts next_nodes) blocks
            |> List.map ~f:(register_node loc)
            |> List.concat )
      | LoopStmt (loc, body_stmts, end_label) ->
          let new_node =
            Procdesc.create_node ctx.proc_desc loc (Procdesc.Node.Skip_node "LoopStmt") []
          in
          let nodes_after_loop = trans_stmts following_nodes stmts |> register_node loc in
          register_label end_label nodes_after_loop ;
          let next_nodes = trans_stmts [new_node] body_stmts |> register_node loc in
          Procdesc.node_set_succs_exn ctx.proc_desc new_node next_nodes [] ;
          Nodes [new_node] )
    | [] ->
        Nodes following_nodes
  in
  let next_nodes =
    trans_stmts [procedure_exit_node] stmts |> register_node (Procdesc.get_loc ctx.proc_desc)
  in
  let set_succs node label =
    match Hashtbl.find label_map label with
    | Some nodes ->
        Procdesc.node_set_succs_exn ctx.proc_desc node nodes []
    | None ->
        L.die InternalError "No label defined for %a" Label.pp label
  in
  Caml.Hashtbl.iter set_succs node_table ;
  Procdesc.node_set_succs_exn ctx.proc_desc procedure_start_node next_nodes []
