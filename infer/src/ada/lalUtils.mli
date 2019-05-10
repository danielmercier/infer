(*
 * Copyright (c) 2017-present, AdaCore.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 *)

open! IStd
open Libadalang

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

val is_access : Identifier.t -> bool
(** Return true if the identifier is refering to 'Access *)

val lvalue_type_expr : [< lvalue] -> TypeExpr.t
(** Return the type expression for an lvalue. When calling p_type_expression on
 * an expression, the BaseType is returned, but not the more precise type.
 *
 * For example for the following declaration:
 * I : Integer range 1 .. 10
 *
 * If p_type_expression is called on I, the type Integer is returned, so we
 * lose the constraint on Integer.
 *
 * This function can be applied on a lvalue and returns the more precise type
 * as a TypeExpr.
 * *)

val is_array_type : [< TypeExpr.t] -> bool
(** Check if the given TypeExpr is a type expression of an array *)

val is_record_type : [< TypeExpr.t] -> bool
(** Check if the given TypeExpr is a type expression of a record *)
