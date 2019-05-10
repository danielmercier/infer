(*
 * Copyright (c) 2017-present, AdaCore.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 *)

open! IStd
open AdaFrontend

(* We define an intermediate control flow graph for convinience, this module
 * contains the function to translate this intermediate representation into
 * the actual infer representation of the control flow graph *)

val trans_cfg : context -> stmt list -> unit
(** Translate the intermediate representation for control flow to infer regular
 * CFG, which is imperative. Thus, calling this modifies the given Procdesc
 * in the given context *)
