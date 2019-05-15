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

let unique_defining_name name =
  let plain = AdaNode.text name in
  match DefiningName.p_basic_decl name >>| BasicDecl.p_unique_identifying_name with
  | Some unique_name ->
      Mangled.mangled plain unique_name
  | None ->
      L.die InternalError "Cannot generate unique defining name for %s" (AdaNode.short_image name)


let field_name name = AdaNode.text (name :> DefiningName.t) |> Typ.Fieldname.Ada.from_string

let is_access attribute = String.equal (String.lowercase (AdaNode.text attribute)) "access"

let rec is_type_def ~f type_expr =
  (* Given a predicate on a type def, return true if the base type def of the
   * given type expression returns true when applied to f *)
  let rec is_type_decl base_type_decl =
    match (base_type_decl :> AdaNode.t) with
    | #TypeDecl.t as type_decl ->
        f (TypeDecl.f_type_def type_decl)
    | `SubtypeDecl {f_subtype= (lazy subtype)} ->
        is_type_def ~f (subtype :> TypeExpr.t)
    | _ ->
        false
  in
  TypeExpr.p_designated_type_decl type_expr >>| is_type_decl |> Option.value ~default:false


let is_array_type type_expr =
  is_type_def ~f:(function `ArrayTypeDef _ -> true | _ -> false) (type_expr :> TypeExpr.t)


let is_record_type type_expr =
  is_type_def ~f:(function `RecordTypeDef _ -> true | _ -> false) (type_expr :> TypeExpr.t)


let is_elementary_type base_type_decl =
  BaseTypeDecl.p_is_discrete_type base_type_decl
  || BaseTypeDecl.p_is_access_type base_type_decl
  || BaseTypeDecl.p_is_real_type base_type_decl


let is_composite_type base_type_decl = not (is_elementary_type base_type_decl)

let sort_params param_actuals =
  (* TODO: This should sort the params but for now there is an issue in
   * Libadalang with the type of ParamActual *)
  param_actuals


let is_record_field_access dotted_name =
  match Name.p_referenced_decl dotted_name with
  | Some (#ComponentDecl.t | #DiscriminantSpec.t) ->
      true
  | _ ->
      false
