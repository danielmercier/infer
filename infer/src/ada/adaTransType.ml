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

let trans_type_decl tenv type_decl =
  let rec aux type_decl =
    match BaseTypeDecl.p_base_type type_decl with
    | Some typ ->
        aux typ
    | None -> (
      match (type_decl :> BaseTypeDecl.t) with
      | `TypeDecl {f_type_def= (lazy (`SignedIntTypeDef _))} ->
          Typ.(mk (Tint IInt))
      | `TypeDecl {f_name= (lazy (Some name))} when String.equal (AdaNode.text name) "Boolean" ->
          Typ.(mk (Tint IBool))
      | _ ->
          unimplemented "trans_type for %s" (AdaNode.short_image type_decl) )
  in
  aux (type_decl :> BaseTypeDecl.t)


let trans_type_expr tenv type_expr =
  match TypeExpr.p_designated_type_decl type_expr with
  | Some type_decl ->
      trans_type_decl tenv type_decl
  | None ->
      L.die InternalError "Cannot generate a type for: %s" (AdaNode.short_image type_expr)
