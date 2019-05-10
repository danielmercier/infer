(*
 * Copyright (c) 2017-present, AdaCore.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 *)

open! IStd
open Libadalang

(* Entry point for the translation of a list of files. This module translates
 * the subprograms by calling the right functions in adaTransStmt *)

val translate : AnalysisContext.t -> string list -> unit
(** translate the given list of files to infer IR *)
