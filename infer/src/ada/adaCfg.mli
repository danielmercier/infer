(*
 * Copyright (c) 2017-present, AdaCore.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 *)

open! IStd
open AdaFrontend

val trans_cfg : context -> stmt list -> unit
(** Translate the intermediate representation for control flow to infer regular
 * CFG, which is imperative. Thus, calling this modifies the given Procdesc
 * in the given context *)
