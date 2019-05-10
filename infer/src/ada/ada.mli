(*
 * Copyright (c) 2017-present, AdaCore.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 *)

open! IStd

(* Entry point of the capture for Ada sources *)

val capture : string -> string list -> unit
(** Run the capture phase for Ada. The first argument is the project filename
 * and the second argument is the list of file names to be analyzed *)
