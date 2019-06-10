(*
 * Copyright (c) 2017-present, AdaCore.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 *)

open! IStd

let recordcpy = Typ.Procname.from_string_c_fun "recordcpy"

let arraycpy = Typ.Procname.from_string_c_fun "arraycpy"
