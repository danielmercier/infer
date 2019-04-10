(*
 * Copyright (c) 2017-present, AdaCore.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 *)

open! IStd
open Libadalang
open AdaFrontend

val trans_stmts : context -> StmtList.t -> stmt list
(** translate a list of libadalang statements to a list of the intermediate CFG
 * representation *)
