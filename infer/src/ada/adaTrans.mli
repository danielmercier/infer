(*
 * Copyright (c) 2017-present, AdaCore.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 *)

open! IStd
open Libadalang

val translate : AnalysisContext.t -> string list -> unit
(** translate the given list of files to infer IR *)
