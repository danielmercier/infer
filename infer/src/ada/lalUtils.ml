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

let is_access attribute = String.equal (String.lowercase (AdaNode.text attribute)) "access"

let rec lvalue_type_expr lvalue =
  let element_type type_expr (element_type : [< TypeDef.t] -> TypeExpr.t) =
    let aux base_type_decl =
      match (base_type_decl :> BaseTypeDecl.t) with
      | #TypeDecl.t as type_decl ->
          element_type (TypeDecl.f_type_def type_decl)
      | _ ->
          raise (Invalid_argument "")
    in
    match type_expr with
    | #AnonymousType.t as anon ->
        aux (AnonymousType.f_type_decl anon :> BaseTypeDecl.t)
    | #SubtypeIndication.t as subtype_indication -> (
      match SubtypeIndication.f_name subtype_indication |> Name.p_referenced_decl with
      | Some (#BaseTypeDecl.t as type_decl) ->
          aux type_decl
      | _ ->
          raise (Invalid_argument "") )
    | #EnumLitSynthTypeExpr.t ->
        raise (Invalid_argument "")
  in
  match (lvalue :> lvalue) with
  | #AttributeRef.t
  | #CharLiteral.t
  | #DottedName.t
  | #Identifier.t
  | #QualExpr.t
  | #StringLiteral.t
  | #TargetName.t -> (
    (* Simply going to the declaration of those nodes and taking the type
     * expression of the declaration works. *)
    match Name.p_referenced_decl lvalue >>= BasicDecl.p_type_expression with
    | Some type_expr ->
        type_expr
    | None ->
        L.die InternalError "Cannot get the type expression for %s" (AdaNode.short_image lvalue) )
  | `ExplicitDeref {f_prefix= (lazy prefix)} -> (
      (* For an explicit deref, the type expression will denote an access
       * but we want the type of the underlying accessed element *)
      let access_type_element_type type_def =
        match (type_def :> TypeDef.t) with
        | `TypeAccessDef {f_subtype_indication= (lazy subtype_indication)} ->
            (subtype_indication :> TypeExpr.t)
        | _ ->
            raise (Invalid_argument "")
      in
      try element_type (lvalue_type_expr prefix) access_type_element_type
      with Invalid_argument _ ->
        L.die InternalError "ExplicitDeref type should be an access type" )
  | `CallExpr {f_name= (lazy name)} -> (
      let array_type_element_type type_def =
        match (type_def :> TypeDef.t) with
        | `ArrayTypeDef {f_component_type= (lazy (`ComponentDef {f_type_expr= (lazy type_expr)}))}
          ->
            (type_expr :> TypeExpr.t)
        | _ ->
            raise (Invalid_argument "")
      in
      try element_type (lvalue_type_expr name) array_type_element_type
      with Invalid_argument _ -> L.die InternalError "CallExpr type should be an array type" )


let lvalue_type_expr lvalue = lvalue_type_expr (lvalue :> lvalue)

let rec is_type_def ~f type_expr =
  (* Given a predicate on a type def, return true if the base type def of the
   * given type expression returns true when applied to f *)
  let rec is_array_type_decl base_type_decl =
    match (base_type_decl :> AdaNode.t) with
    | #TypeDecl.t as type_decl ->
        f (TypeDecl.f_type_def type_decl)
    | `SubtypeDecl {f_subtype= (lazy subtype)} ->
        is_type_def ~f (subtype :> TypeExpr.t)
    | _ ->
        false
  in
  match (type_expr :> TypeExpr.t) with
  | #SubtypeIndication.t as subtype ->
      SubtypeIndication.f_name subtype |> Name.p_referenced_decl >>| is_array_type_decl
      |> Option.value ~default:false
  | #AnonymousType.t as anon ->
      is_array_type_decl (AnonymousType.f_type_decl anon)
  | #EnumLitSynthTypeExpr.t ->
      false


let is_array_type type_expr =
  is_type_def ~f:(function `ArrayTypeDef _ -> true | _ -> false) (type_expr :> TypeExpr.t)


let is_record_type type_expr =
  is_type_def ~f:(function `RecordTypeDef _ -> true | _ -> false) (type_expr :> TypeExpr.t)
