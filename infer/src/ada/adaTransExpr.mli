(*
 * Copyright (c) 2017-present, AdaCore.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 *)

open! IStd
open Libadalang
open LalUtils
open AdaFrontend

(** Entry point for the translation of expressions into infer ir statements
 * and expressions.
 *
 * Epressions can make some control flow,
 *
 * For example A and then B
 *
 * Thus, we need to use an intermediate representation (see expr type) to
 * represent expressions.
 *
 * This module also uses a structured continuation to be able to say what we
 * want to do with the translation of some expression (see continuation type) *)

val trans_lvalue : context -> [< lvalue] -> stmt list * (Sil.instr list * Exp.t)
(** An lvalue is an expression that have some location in the memory. Translate
 * on of those to an expression symbolically representing this location. *)

(** The translation of an expression can either be a simple expression,
 * or an If expression with an conditional expression and expression for when the
 * condition is true, of false. A simple expression is either an infer Exp, or
 * a Boolean insterted by the frontend
 *
 * We make this distinction of boolean inserted by the frontend because we don't
 * want to create dead blocks when translating an expression. *)
type simple_expr = Exp of Sil.instr list * Exp.t | Bool of bool

type expr = SimpleExpr of simple_expr | If of Sil.instr list * Exp.t * (expr * expr)

val of_exp : Sil.instr list -> Exp.t -> expr
(** transform a sil instruction list and an expression to an expr *)

val of_bool : bool -> expr
(** transform a boolean to an expr *)

val to_exp : simple_expr -> Sil.instr list * Exp.t
(** transform a simple expression to a sil instruction list and an infer Exp *)

val mk_not : Exp.t -> Exp.t
(** Return the complement of the given expression, by simplifying it if possible *)

val load : Typ.t -> Location.t -> Exp.t -> Sil.instr list * Exp.t
(** return instruction to load the given exp in an ident and return an exp
 * representing this ident. *)

(** Type used to call mk_array_access to access a field of the array *)
type array_access = Data | First | Last | Length

val mk_array_access : context -> Typ.t -> Exp.t -> array_access -> Typ.t * Exp.t
(** Compute the access to the desired field of the given lvalue assuming
 * it is an array. *)

(** A value of this type is passed to the translation of the expression. It says
 * what will be done with the translated expression.
 *    - Goto is meaningfull only for boolean expressions. The expression is
 *       translated to different branches in which the expression is evaluated to
 *       true or false. At the end of each branch in which the expression is evaluated
 *       to true, there is a goto to the first label, and the second label for false.
 *
 *    - Tmp means that the caller wants the result of the expression to be in
 *       an tmp variable if necessary. It is necessary when the expression makes
 *       some control flow.
 *
 *    - Inline means that the caller will use the expression as it is. This means
 *       that for example, for one assignment, the assignment could be duplicated
 *       if some control flow happened. *)
type _ continuation =
  | Goto : jump_kind * jump_kind -> unit continuation
  | Tmp : string -> (Sil.instr list * Exp.t) continuation
  | Inline : expr continuation

val map_to_stmts : f:(simple_expr -> stmt list) -> Location.t -> expr -> stmt list
(** transform an expression to a list of statements by calling f on the leafs *)

val trans_expr : context -> 'a continuation -> [< Expr.t] -> stmt list * 'a
(** Translate an expression to an intermediate representation. *)

val trans_bounds_from_discrete :
  context -> AdaType.discrete -> stmt list * Sil.instr list * Exp.t * Exp.t

val trans_bounds :
  context -> [< Expr.t | SubtypeIndication.t] -> stmt list * Sil.instr list * Exp.t * Exp.t
(** Translate either a subtype indication of a scalar type, or an expression into
 * a pair of expressions that represent the first and the last value of this expression.
 *
 * An example of expression is:
 * 1 .. 10
 * this will return the pair 1, 10
 *
 * A subtype indication is for example:
 * Integer range 15 .. 20
 * in that case it will return 15, 20 *)

val trans_membership_expr :
     context
  -> 'a continuation
  -> Typ.t
  -> Location.t
  -> expr
  -> [< Expr.t | SubtypeIndication.t] list
  -> stmt list * 'a
(** A membership expression is of the form:
  * X in A | B | C,
  *
  * this function translates this expression by taking the list of
  * [A; B; C]
  *
  * This is translated by calling trans_bounds on each element of this list *)

val range_check : context -> Location.t -> AdaType.discrete -> Sil.instr list -> Exp.t -> stmt list
(** Return a stmt corresponding to a range check of the given infer expr and the
 * given discrete type *)

val type_of_expr : context -> [< Expr.t] -> Typ.t
(** Compute the type of the given lal expression *)
