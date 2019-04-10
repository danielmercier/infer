(*
 * Copyright (c) 2017-present, AdaCore.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 *)

open! IStd
open Libadalang
open AdaFrontend
module L = Logging

val trans_type_decl : Tenv.t -> [< BaseTypeDecl.t] -> Typ.t
(** Translate a base type declaration to an IR type *)

val trans_type_expr : Tenv.t -> [< TypeExpr.t] -> Typ.t
(** Translate a type expression to an IR type *)
