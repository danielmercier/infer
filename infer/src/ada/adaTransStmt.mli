(*
 * Copyright (c) 2017-present, AdaCore.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 *)

open! IStd
open Libadalang
open AdaFrontend

(** Entry point for the translation of statements into our intermediate
 * representation.
 *
 * This module uses functions inside the adaTransExpr module to translate
 * expression and make statements out of them *)

val trans_stmts : context -> StmtList.t -> stmt list
(** translate a list of libadalang statements to a list of the intermediate CFG
 * representation *)

val trans_decls : context -> DeclarativePart.t -> stmt list
(** translate the given declaration part to a list of statements *)
