(*
 * Copyright (c) 2017-present, AdaCore.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 *)

open! IStd
open Libadalang
open LalUtils
open AdaType
open Option.Monad_infix
module L = Logging
module F = Format

(* Type for values that can represent addresses *)
type lvalue =
  [ AttributeRef.t
  | CallExpr.t
  | CharLiteral.t
  | DottedName.t
  | ExplicitDeref.t
  | Identifier.t
  | QualExpr.t
  | StringLiteral.t
  | TargetName.t ]

(** A parameter can either be passed by copy or by reference. This type is
 * used to differenciate both passing methods *)
type param_mode = Copy | Reference

(** Map a mode of a function to the parameter passing strategy *)
let param_mode typ = function
  | Some (`ModeInOut _) | Some (`ModeOut _) ->
      Reference
  | Some (`ModeDefault _) | Some (`ModeIn _) | None ->
      (* Always pass arrays and records by reference *)
      if is_record_type typ || is_array_type typ then Reference else Copy


module Label = Int
module DefiningNameMap = Caml.Map.Make (DefiningName)
module DefiningNameTable = Caml.Hashtbl.Make (DefiningName)

type tenvs = {infer_tenv: Tenv.t; ada_tenv: AdaType.tenv}

(** The context is passed around for the translation of a subprograms, it contains:
  * - cfg: the current infer control flow graph of the supbrogram.
  * - infer_tenv: the infer type environement.
  * - ada_tenv: the ada type environement from AdaType.
  * - source_file: the infer source file in which the procedure is located.
  * - proc_desc: the infer procedure description of the one being translated.
  * - params_modes: A table that maps a defining name referencing a parameter,
  *   to its mode, either passed by copy, or by reference.
  * - ret_type: If this is a context for a function, this is the type expression
  *   of the returned value. Otherwise it is None.
  * - label_table: an hash table that maps a label in the original source code,
  *   to a label in the intermediate CFG representation.
  * - loop_map: Loops can have names, this map, maps the name of a loop to
  *   the label of the end of the loop to use in ExitStmt.
  * - current_loop: If we are translating the body of a loop, this is equal
  *   to the inner most loop end label that we are translating.
  * - subst: A substitution map that should be used to get a program variable
  *   from a name. If the map doesn't contain a pvar for the given name, then
  *   a generic one can be created. This is used for ExtendedReturnStmt where
  *   the name of the variable is mapped to the "return" infer identifier.*)
type context =
  { cfg: Cfg.t
  ; tenvs: tenvs
  ; source_file: SourceFile.t
  ; proc_desc: Procdesc.t
  ; params_modes: param_mode DefiningNameMap.t
  ; ret_type: TypeExpr.t option
  ; label_table: Label.t DefiningNameTable.t
  ; loop_map: Label.t DefiningNameMap.t
  ; current_loop: Label.t option
  ; subst: Pvar.t DefiningNameMap.t }

let mk_context cfg tenvs source_file proc_desc params_modes ret_type =
  { cfg
  ; tenvs
  ; source_file
  ; proc_desc
  ; params_modes
  ; ret_type= (ret_type :> TypeExpr.t option)
  ; label_table= DefiningNameTable.create 24
  ; loop_map= DefiningNameMap.empty
  ; current_loop= None
  ; subst= DefiningNameMap.empty }


(** Creates a new, fresh label *)
let mk_label =
  let lbl = ref 0 in
  fun () ->
    lbl := !lbl + 1 ;
    !lbl


(** The given name is assumed to be a label name. If a label is already
 * register for this name, return it. Otherwise, create a new label, register
 * it and return it. *)
let find_or_add ctx name =
  match DefiningNameTable.find_opt ctx.label_table (name :> DefiningName.t) with
  | Some label ->
      label
  | None ->
      let label = mk_label () in
      DefiningNameTable.add ctx.label_table (name :> DefiningName.t) label ;
      label


type jump_kind = Next | Label of Label.t | Exit

type stmt =
  | Block of block
  | Label of Location.t * Label.t
  | Jump of Location.t * jump_kind
  | Split of Location.t * stmt list list
  | LoopStmt of Location.t * stmt list * Label.t

and block = {instrs: Sil.instr list; loc: Location.t; nodekind: Procdesc.Node.nodekind}

let location source_file node =
  let sloc_range = AdaNode.sloc_range node in
  Location.{line= sloc_range.loc_start.line; col= sloc_range.loc_start.column; file= source_file}


let end_location source_file node =
  let sloc_range = AdaNode.sloc_range node in
  Location.{line= sloc_range.loc_end.line; col= sloc_range.loc_end.column; file= source_file}


let map_params ~f params =
  let f param =
    let type_expr = ParamSpec.f_type_expr param in
    let mode = ParamSpec.f_mode param in
    ParamSpec.f_ids param |> DefiningNameList.f_list
    |> List.map ~f:(fun name -> f (name, type_expr, mode))
  in
  Params.f_params params |> ParamSpecList.f_list |> List.map ~f |> List.concat


let infer_typ_of_type_decl tenvs base_type_decl =
  trans_type_decl tenvs.ada_tenv base_type_decl |> to_infer_typ tenvs.ada_tenv tenvs.infer_tenv


let infer_typ_of_type_expr tenvs type_expr =
  trans_type_expr tenvs.ada_tenv type_expr |> to_infer_typ tenvs.ada_tenv tenvs.infer_tenv


let unique_type_name type_expr =
  match
    TypeExpr.p_type_name type_expr >>= Name.p_referenced_decl
    >>| BasicDecl.p_unique_identifying_name
  with
  | Some unique_name ->
      unique_name
  | None ->
      (* If not, use the short_image of the node. The short image contains the
       * position of the node *)
      AdaNode.short_image type_expr


let get_proc_name body =
  let spec = BaseSubpBody.f_subp_spec body in
  let unique_name = BasicDecl.p_unique_identifying_name body in
  let simple_name =
    match SubpSpec.f_subp_name spec with Some name -> AdaNode.text name | None -> unique_name
  in
  let params =
    match SubpSpec.f_subp_params spec with
    | Some params ->
        map_params ~f:(fun (_, typ, _) -> unique_type_name typ) params
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


let pvar ctx node =
  let pvar_for_name name =
    match DefiningNameMap.find_opt name ctx.subst with
    | Some pvar ->
        pvar
    | None -> (
        let pvar_name = unique_defining_name name in
        match get_defining_name_proc name with
        | Some proc_name ->
            Pvar.mk pvar_name proc_name
        | None ->
            Pvar.mk_global pvar_name )
  in
  match (node :> AdaNode.t) with
  | #DefiningName.t as name ->
      pvar_for_name name
  | _ -> (
    match AdaNode.p_xref node with
    | Some name ->
        pvar_for_name name
    | None ->
        L.die InternalError "Cannot generate a program variable for node %s"
          (AdaNode.short_image node) )


let rec pp_stmt fmt stmt =
  match stmt with
  | Block {instrs} ->
      F.fprintf fmt "@[<v>@[<v 2>Block {@ %a@]@ }@]"
        (F.pp_print_list (Sil.pp_instr ~print_types:true Pp.text))
        instrs
  | Label (_, label) ->
      F.fprintf fmt "@[%a:@]" Label.pp label
  | Jump (_, Next) ->
      F.fprintf fmt "@[Goto Next@]"
  | Jump (_, Label label) ->
      F.fprintf fmt "@[Goto @[%a@]@]" Label.pp label
  | Jump (_, Exit) ->
      F.fprintf fmt "@[Goto Exit@]"
  | Split (_, stmts_list) ->
      let pp_sep fmt () = F.fprintf fmt "@]@ @[<v 2>} {@ " in
      F.fprintf fmt "@[<v>@[<v 2>Split {@ %a@]@ }@]" (F.pp_print_list ~pp_sep pp) stmts_list
  | LoopStmt (_, stmts, label) ->
      F.fprintf fmt "@[<v>@[<v 2>LoopStmt {@ %a@]@ } end: %a@]" pp stmts Label.pp label


and pp fmt stmts = Format.fprintf fmt "@[<v>%a@]" (Format.pp_print_list pp_stmt) stmts
