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
module DefiningNameMap = Caml.Map.Make (DefiningName)
module DefiningNameTable = Caml.Hashtbl.Make (DefiningName)

(** The context is passed around for the translation of a subprograms, it contains:
  * - cfg: the current infer control flow graph of the supbrogram.
  * - tenv: the infer type environement.
  * - source_file: the infer source file in which the procedure is located.
  * - proc_desc: the infer procedure description of the one being translated.
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
  ; tenv: Tenv.t
  ; source_file: SourceFile.t
  ; proc_desc: Procdesc.t
  ; ret_type: TypeExpr.t option
  ; label_table: Label.t DefiningNameTable.t
  ; loop_map: Label.t DefiningNameMap.t
  ; current_loop: Label.t option
  ; subst: Pvar.t DefiningNameMap.t }

let mk_context cfg tenv source_file proc_desc ret_type =
  { cfg
  ; tenv
  ; source_file
  ; proc_desc
  ; ret_type= (ret_type :> TypeExpr.t option)
  ; label_table= DefiningNameTable.create 24
  ; loop_map= DefiningNameMap.empty
  ; current_loop= None
  ; subst= DefiningNameMap.empty }


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


let field_name name = AdaNode.text (name :> DefiningName.t) |> Typ.Fieldname.Ada.from_string

let sort_params _ param_actuals =
  (* TODO: This should sort the params but for now there is an issue in
   * Libadalang with the type of ParamActual *)
  List.map ~f:(fun {ParamActual.actual} -> actual) param_actuals


let is_access attribute = String.equal (String.lowercase (AdaNode.text attribute)) "access"

let lvalue_type_expr lvalue =
  let type_expr =
    match Name.p_referenced_decl lvalue >>= BasicDecl.p_type_expression with
    | Some type_expr ->
        type_expr
    | None ->
        L.die InternalError "Cannot get the type expression for %s" (AdaNode.short_image lvalue)
  in
  match lvalue with
  | #AttributeRef.t
  | #CallExpr.t
  | #CharLiteral.t
  | #DottedName.t
  | #Identifier.t
  | #QualExpr.t
  | #StringLiteral.t
  | #TargetName.t ->
      type_expr
  | #ExplicitDeref.t -> (
      (* For an explicit deref, the type expression will denote an access
       * but we want the type of the underlying accessed element *)
      let access_type_element_type base_type_decl =
        match (base_type_decl :> BaseTypeDecl.t) with
        | #TypeDecl.t as type_decl -> (
          match TypeDecl.f_type_def type_decl with
          | `TypeAccessDef {TypeAccessDefType.f_subtype_indication= (lazy subtype_indication)} ->
              (subtype_indication :> TypeExpr.t)
          | _ ->
              L.die InternalError "ExplicitDeref type should be an access type" )
        | _ ->
            L.die InternalError "ExplicitDeref type should be an access type"
      in
      match type_expr with
      | #AnonymousType.t as anon ->
          access_type_element_type (AnonymousType.f_type_decl anon)
      | #SubtypeIndication.t as subtype_indication -> (
        match SubtypeIndication.f_name subtype_indication |> Name.p_referenced_decl with
        | Some (#BaseTypeDecl.t as type_decl) ->
            access_type_element_type type_decl
        | _ ->
            L.die InternalError "ExplicitDeref type should be an access type" )
      | #EnumLitSynthTypeExpr.t ->
          L.die InternalError "ExplicitDeref type should be an access type" )


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
