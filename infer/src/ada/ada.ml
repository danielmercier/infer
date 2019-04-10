(*
 * Copyright (c) 2017-present, AdaCore.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 *)

open! IStd
open Libadalang
module L = Logging

let capture prog args =
  match args with
  | "-P" :: project_name :: (file :: other_files as source_files) ->
      let unit_provider = UnitProvider.for_project project_name in
      let ctx = AnalysisContext.create ~unit_provider () in
      AdaTrans.translate ctx source_files
  | _ ->
      L.die InternalError "Should be called with: %s -P PROJECT FILE FILE..." prog
