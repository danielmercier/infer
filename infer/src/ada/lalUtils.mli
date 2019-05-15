(*
 * Copyright (c) 2017-present, AdaCore.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 *)

open! IStd
open Libadalang

(** This module contains some utility types and functions related to our use
 * of libadalang. Note that some of them should be implemented as
 * properties in the future. *)

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

val unique_defining_name : [< DefiningName.t] -> Mangled.t
(** Given a defining name, return a string that identifies uniquely the name *)

val field_name : [< DefiningName.t] -> Typ.Fieldname.t
(** From a defining name that represents a field in a record, return the the name
 * of this field *)

val is_access : Identifier.t -> bool
(** Return true if the identifier is refering to 'Access *)

val is_array_type : [< TypeExpr.t] -> bool
(** Check if the given TypeExpr is a type expression of an array *)

val is_record_type : [< TypeExpr.t] -> bool
(** Check if the given TypeExpr is a type expression of a record *)

val is_elementary_type : [< BaseTypeDecl.t] -> bool
(** Return true if the given type is elementary:
  *   - scalar
  *   - real
  *   - access *)

val is_composite_type : [< BaseTypeDecl.t] -> bool
(** Return true if the given type is composite (not elementary)
  *   - record
  *   - array *)

val sort_params : ParamActual.t list -> ParamActual.t list
(** Given a param to actual mapping list, return the actuals in the order of
 * the procedure description *)

val is_record_field_access : [< DottedName.t] -> bool
(** Given a dotted name, return true if it represents an access to a record *)
