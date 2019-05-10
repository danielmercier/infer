(*
 * Copyright (c) 2017-present, AdaCore.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 *)

open! IStd
open Libadalang

(* This module contains the definition of multiple types usefull for the
 * translation of ada sources. It also defines some helper functions for
 * conveniance *)

val unimplemented : ('a, Format.formatter, unit, _) format4 -> 'a

(** A parameter can either be passed by copy or by reference. This type is
 * used to differenciate both passing methods *)
type param_mode = Copy | Reference

val param_mode : [< TypeExpr.t] -> Mode.t option -> param_mode
(** Map a the type and the mode of a function parameter to the passing strategy *)

module Label = Int

module DefiningNameMap : Caml.Map.S with type key = DefiningName.t

module DefiningNameTable : Caml.Hashtbl.S with type key = DefiningName.t

(** The context is passed around for the translation of a subprograms, it contains:
  * - cfg: the current infer control flow graph of the supbrogram.
  * - tenv: the infer type environement.
  * - source_file: the infer source file in which the procedure is located.
  * - proc_desc: the infer procedure description of the one being translated.
  * - params_modes: A table that maps a defining name referencing a parameter,
  *   to its mode, either passed by copy, or by reference.
  * - ret_type: If this is a context for a function, this is the type expression
  *   of the returned value. Otherwise it is None.
  * - label_table: an hash table that maps a label in the original source code,
  *   to a label in the intermediate CFG representation.
  * - loop_map: Loops can have names, this map, maps the name of a loop to
  *   the label of the end of the loop to use in ExitStmt.
  * - current_loop: If we are translating the body of a loop, this is equal
  *   to the inner most loop end label that we are translating.
  * - subst: A substitution map that should be used to get a program variable
  *   from a name. If the map doesn't contain a pvar for the given name, then
  *   a generic one can be created. This is used for ExtendedReturnStmt where
  *   the name of the variable is mapped to the "return" infer identifier.*)
type context =
  { cfg: Cfg.t
  ; tenv: Tenv.t
  ; source_file: SourceFile.t
  ; proc_desc: Procdesc.t
  ; params_modes: param_mode DefiningNameMap.t
  ; ret_type: TypeExpr.t option
  ; label_table: Label.t DefiningNameTable.t
  ; loop_map: Label.t DefiningNameMap.t
  ; current_loop: Label.t option
  ; subst: Pvar.t DefiningNameMap.t }

val mk_context :
     Cfg.t
  -> Tenv.t
  -> SourceFile.t
  -> Procdesc.t
  -> param_mode DefiningNameMap.t
  -> [< TypeExpr.t] option
  -> context
(** Creates a new context with given arguments *)

val mk_label : unit -> Label.t
(** Creates a new fresh label *)

val find_or_add : context -> [< DefiningName.t] -> Label.t
(** Find the label for the given defining name. If it does not exists, add a new one
 * to the context and return it *)

(** At the end of a block, the control flow can either:
  *   Next: Go to the next instruction
  *   Label l: Go to the block registerd by the label l
  *   Exit: Go at the exit of the procedure *)
type jump_kind = Next | Label of Label.t | Exit

(** We use this intermediate representation for the control flow.
 * Afterwards, this is translated to infer's control flow which is represented
 * imperatively in the Procdesc. *)
type stmt =
  | Block of block
  | Label of Location.t * Label.t
  | Jump of Location.t * jump_kind
  | Split of Location.t * stmt list list
  | LoopStmt of Location.t * stmt list * Label.t

and block = {instrs: Sil.instr list; loc: Location.t; nodekind: Procdesc.Node.nodekind}

val location : SourceFile.t -> [< AdaNode.t] -> Location.t
(** Create a location from the given AdaNode. Since the location contains only
 * one source location, we use the start location of the given AdaNode *)

val end_location : SourceFile.t -> [< AdaNode.t] -> Location.t
(** Create a location from the given AdaNode. Since the location contains only
 * one source location, we use the end location of the given AdaNode *)

val map_params :
     f:(   DefiningName.t
           * [ AnonymousType.t
             | ConstrainedSubtypeIndication.t
             | DiscreteSubtypeIndication.t
             | SubtypeIndication.t ]
           * Mode.t option
        -> 'a)
  -> [< Params.t]
  -> 'a list
(** given a Params.t, create a list, calling for each parameter the function f.
 * The pair being the name of the parameter and it's type. *)

val unique_type_name : [< TypeExpr.t] -> string
(** Given a type expression, return a string that identifies uniquely, this type *)

val unique_defining_name : [< DefiningName.t] -> Mangled.t
(** Given a defining name, return a string that identifies uniquely the name *)

val pvar : context -> [< AdaNode.t] -> Pvar.t
(** Given any AdaNode, calling p_xref, try to make a program variable of it.
 * Also use the substitute map in the context to use a particular program variable
 * if required *)

val get_proc_name : [< BaseSubpBody.t] -> Typ.Procname.t
(** Return a Typ.Procname.t from a supbrogram body *)

val get_defining_name_proc : [< DefiningName.t] -> Typ.Procname.t option
(** Return the procedure that declares the given name. Return None if the name
 * is global. *)

val field_name : [< DefiningName.t] -> Typ.Fieldname.t
(** From a defining name that represents a field in a record, return the the name
 * of this field *)

val sort_params : Procdesc.t -> ParamActual.t list -> ParamActual.t list
(** Given a param to actual mapping list, return the actuals in the order of
 * the procedure description *)

val pp : Format.formatter -> stmt list -> unit
