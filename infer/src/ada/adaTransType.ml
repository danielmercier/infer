(*
 * Copyright (c) 2017-present, AdaCore.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 *)

open! IStd
open Libadalang
open AdaFrontend
open Option.Monad_infix
module L = Logging

let rec trans_type_decl_ tenv type_decl =
  match BaseTypeDecl.p_base_type type_decl with
  | Some typ ->
      trans_type_decl_ tenv typ
  | None -> (
    match (type_decl :> BaseTypeDecl.t) with
    | `TypeDecl {f_type_def= (lazy #SignedIntTypeDef.t)} ->
        Typ.(mk (Tint IInt))
    | `TypeDecl {f_type_def= (lazy #EnumTypeDef.t)} ->
        Typ.(mk (Tint IInt))
    | `TypeDecl {f_name= (lazy (Some name))} when String.equal (AdaNode.text name) "Boolean" ->
        Typ.(mk (Tint IBool))
    | `TypeDecl {f_type_def= (lazy (`TypeAccessDef {f_subtype_indication= (lazy subtype)}))} -> (
      match SubtypeIndication.f_name subtype |> Name.p_referenced_decl with
      | Some (#BaseTypeDecl.t as base_type) ->
          Typ.(mk (Tptr (trans_type_decl_ tenv base_type, Pk_pointer)))
      | _ ->
          L.die InternalError "Cannot generate a type for %s" (AdaNode.short_image type_decl) )
    | `TypeDecl {f_name= (lazy (Some name)); f_type_def= (lazy #RecordTypeDef.t)} ->
        Typ.mk (Typ.Tstruct (Typ.AdaRecord (unique_defining_name name)))
    | `TypeDecl
        { f_type_def=
            (lazy
              (`ArrayTypeDef
                {f_component_type= (lazy (`ComponentDef {f_type_expr= (lazy type_expr)}))})) } ->
        (* TODO: translate static length arrays and use fixed length *)
        Typ.mk
          (Typ.Tarray
             {elt= trans_type_expr_ tenv (type_expr :> TypeExpr.t); length= None; stride= None})
    | `SubtypeDecl {f_subtype= (lazy subtype)} -> (
        let name = SubtypeIndication.f_name subtype in
        match AdaNode.p_xref name >>= DefiningName.p_basic_decl with
        | Some (#BaseTypeDecl.t as subtype_decl) ->
            trans_type_decl_ tenv subtype_decl
        | Some subtype_decl ->
            unimplemented "trans_type for %s" (AdaNode.short_image subtype_decl)
        | None ->
            L.die InternalError "Cannot generate a type for %s" (AdaNode.short_image type_decl) )
    | _ ->
        unimplemented "trans_type for %s" (AdaNode.short_image type_decl) )


and trans_type_expr_ tenv type_expr =
  match TypeExpr.p_designated_type_decl type_expr with
  | Some type_decl ->
      trans_type_decl_ tenv type_decl
  | None ->
      L.die InternalError "Cannot generate a type for: %s" (AdaNode.short_image type_expr)


let trans_type_decl tenv type_decl = trans_type_decl_ tenv (type_decl :> BaseTypeDecl.t)

let trans_type_expr tenv type_expr = trans_type_expr_ tenv (type_expr :> TypeExpr.t)
