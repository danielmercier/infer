(*
 * Copyright (c) 2017-present, AdaCore.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 *)

open! IStd
open Libadalang

(** kind of an array index *)
type index_kind = Fixed | Dynamic

(** the discriminant is a field *)
type discriminant = Typ.Fieldname.t

(** a expr is use to represent an expression for types *)
type expr = Int of int | Lal of Expr.t

type range = expr * expr

(** a condition on a variant part can either be a simple expression, a range,
 * or an upper bound (not included) *)
type condition = Equal of expr | InRange of range | LessThan of expr

(** a discrete type is either a signed integer, a modulo integer or an enum *)
type discrete = Signed of range | Enum of expr (* Length of the enum *) | Mod of expr

(** a field of a record contains it's name, the list of condition for this field
 * to be possible to access and the type of the field *)
type field = {name: Typ.Fieldname.t; condition: (discriminant * condition) list; typ: t}

(** a record is composed of some discriminant, each discriminant have:
  *   - a name
  *   - a discrete type
  *   - a possible expr which means that the discriminant is fixed for this type *)
and record = {discriminants: (discriminant * discrete * expr option) list; fields: field list}

(** tenv is the type environement where the record definitions are stored *)
and tenv

(** the differente possible Ada types *)
and t =
  | Discrete of discrete
  | Float
  | Array of Typ.Name.t * (index_kind * discrete) list * t
  | Record of Typ.Name.t
  | Access of t
  | Void

val create : unit -> tenv

val lookup : tenv -> Typ.Name.t -> record option
(** Lookup a record definition registered in the type environment *)

type any_field = Discriminant of discriminant * discrete * expr option | Field of field

val lookup_field : tenv -> Typ.Name.t -> Typ.Fieldname.t -> any_field option
(** Lookup a field from a record definition registered in the type environment *)

val field_typ : any_field -> t
(** Return the type for a discriminant or a regular field *)

val trans_type_decl : tenv -> [< BaseTypeDecl.t] -> t
(** Return a type from a lal base type declaration *)

val trans_type_expr : tenv -> [< TypeExpr.t] -> t
(** Return a type from a lal type expression *)

val trans_type_of_expr : tenv -> [< Expr.t] -> t
(** Return the precise type for the given expression *)

val to_infer_typ : tenv -> Tenv.t -> t -> Typ.t
(** Translate an ada type to the representation of types in infer. If
  * necessary, this function also updates the given infer type environement*)

val pp : tenv -> Format.formatter -> t -> unit
