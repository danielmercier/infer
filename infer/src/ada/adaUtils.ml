(*
 * Copyright (c) 2017-present, AdaCore.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 *)

open! IStd
module F = Format
module L = Logging

let unimplemented fmt =
  F.kasprintf (fun msg -> L.die InternalError "%s is not implemented" msg) fmt
