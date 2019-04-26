(*
 * Copyright (c) 2017-present, AdaCore.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 *)

open! IStd
open Libadalang
open Option.Monad_infix
module L = Logging
module F = Format

let unimplemented fmt =
  F.kasprintf (fun msg -> L.die InternalError "%s is not implemented" msg) fmt


module Label = Int
module LoopMap = Caml.Map.Make (DefiningName)
module DefiningNameTable = Caml.Hashtbl.Make (DefiningName)

type context =
  { cfg: Cfg.t
  ; tenv: Tenv.t
  ; source_file: SourceFile.t
  ; proc_desc: Procdesc.t
  ; label_table: Label.t DefiningNameTable.t
  ; loop_map: Label.t LoopMap.t
  ; current_loop: Label.t option }

let mk_context cfg tenv source_file proc_desc =
  { cfg
  ; tenv
  ; source_file
  ; proc_desc
  ; label_table= DefiningNameTable.create 24
  ; loop_map= LoopMap.empty
  ; current_loop= None }


let mk_label =
  let lbl = ref 0 in
  fun () ->
    lbl := !lbl + 1 ;
    !lbl


let find_or_add ctx name =
  match DefiningNameTable.find_opt ctx.label_table (name :> DefiningName.t) with
  | Some label ->
      label
  | None ->
      let label = mk_label () in
      DefiningNameTable.add ctx.label_table (name :> DefiningName.t) label ;
      label


type jump_kind = Next | Label of Label.t | Exit

(** We use this intermediate representation for the control flow.
 * Afterwards, this is translated to infer's control flow which is represented
 * imperatively in the Procdesc. *)
type stmt = Block of block | Label of Label.t | Jump of jump_kind | Split of stmt list list

and block = {instrs: Sil.instr list; loc: Location.t; nodekind: Procdesc.Node.nodekind}

let location source_file node =
  let sloc_range = AdaNode.sloc_range node in
  Location.{line= sloc_range.loc_start.line; col= sloc_range.loc_start.column; file= source_file}


let map_params ~f params =
  let f param =
    let type_expr = ParamSpec.f_type_expr param in
    ParamSpec.f_ids param |> DefiningNameList.f_list
    |> List.map ~f:(fun name -> f (name, type_expr))
  in
  Params.f_params params |> ParamSpecList.f_list |> List.map ~f |> List.concat


let unique_type_name type_expr =
  match
    TypeExpr.p_type_name type_expr >>= Name.p_referenced_decl
    >>| BasicDecl.p_unique_identifying_name
  with
  | Some unique_name ->
      unique_name
  | None ->
      L.die InternalError "Cannot generate unique type name for %s" (AdaNode.short_image type_expr)


let unique_defining_name name =
  let plain = AdaNode.text name in
  match DefiningName.p_basic_decl name >>| BasicDecl.p_unique_identifying_name with
  | Some unique_name ->
      Mangled.mangled plain unique_name
  | None ->
      L.die InternalError "Cannot generate unique defining name for %s" (AdaNode.short_image name)


(** Translate a BaseSubpBody to an infer procedure name *)
let get_proc_name body =
  let spec = BaseSubpBody.f_subp_spec body in
  let unique_name = BasicDecl.p_unique_identifying_name body in
  let simple_name =
    match SubpSpec.f_subp_name spec with Some name -> AdaNode.text name | None -> unique_name
  in
  let params =
    match SubpSpec.f_subp_params spec with
    | Some params ->
        map_params ~f:(fun (_, typ) -> unique_type_name typ) params
    | None ->
        []
  in
  let return = SubpSpec.f_subp_returns spec >>| unique_type_name in
  Typ.Procname.Ada (Typ.Procname.Ada.make (Mangled.mangled simple_name unique_name) params return)


let get_defining_name_proc name =
  let rec aux = function
    | #BaseSubpBody.t as subp ->
        Some (get_proc_name subp)
    | _ as node ->
        AdaNode.parent node >>= aux
  in
  AdaNode.parent name >>= aux


let rec pp_stmt fmt stmt =
  match stmt with
  | Block {instrs} ->
      F.fprintf fmt "@[<v>@[<v 2>Block {@ %a@]@ }@]"
        (F.pp_print_list (Sil.pp_instr ~print_types:true Pp.text))
        instrs
  | Label label ->
      F.fprintf fmt "@[%a:@]" Label.pp label
  | Jump Next ->
      F.fprintf fmt "@[Goto Next@]"
  | Jump (Label label) ->
      F.fprintf fmt "@[Goto @[%a@]@]" Label.pp label
  | Jump Exit ->
      F.fprintf fmt "@[Goto Exit@]"
  | Split stmts_list ->
      let pp_sep fmt () = F.fprintf fmt "@]@ @[<v 2>} {@ " in
      F.(fprintf fmt "@[<v>@[<v 2>Split {@ %a@]@ }@]" (pp_print_list ~pp_sep pp) stmts_list)


and pp fmt stmts = Format.fprintf fmt "@[<v>%a@]" (Format.pp_print_list pp_stmt) stmts
