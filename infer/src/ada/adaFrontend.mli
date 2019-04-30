(*
 * Copyright (c) 2017-present, AdaCore.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 *)

open! IStd
open Libadalang

val unimplemented : ('a, Format.formatter, unit, _) format4 -> 'a

module Label = Int

module DefiningNameMap : Caml.Map.S with type key = DefiningName.t

module DefiningNameTable : Caml.Hashtbl.S with type key = DefiningName.t

type context =
  { cfg: Cfg.t
  ; tenv: Tenv.t
  ; source_file: SourceFile.t
  ; proc_desc: Procdesc.t
  ; label_table: Label.t DefiningNameTable.t
  ; loop_map: Label.t DefiningNameMap.t
  ; current_loop: Label.t option
  ; subst: Pvar.t DefiningNameMap.t }

val mk_context : Cfg.t -> Tenv.t -> SourceFile.t -> Procdesc.t -> context
(** Creates a new context with given arguments *)

val mk_label : unit -> Label.t
(** Creates a new fresh label *)

val find_or_add : context -> [< DefiningName.t] -> Label.t
(** Find the label for the given defining name. If it does not exists, add a new one
 * to the context and return it *)

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

val sort_params : Procdesc.t -> ParamActual.t list -> Expr.t list
(** Given a param to actual mapping list, return the actuals in the order of
 * the procedure description *)

val is_access : Identifier.t -> bool
(** Return true if the identifier is refering to 'Access *)

val pp : Format.formatter -> stmt list -> unit
