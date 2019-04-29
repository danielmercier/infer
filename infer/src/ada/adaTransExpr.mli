(*
 * Copyright (c) 2017-present, AdaCore.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 *)

open! IStd
open Libadalang
open AdaFrontend

val trans_dest :
     context
  -> [< AttributeRef.t
     | CallExpr.t
     | CharLiteral.t
     | DottedName.t
     | ExplicitDeref.t
     | Identifier.t
     | QualExpr.t
     | StringLiteral.t
     | TargetName.t
     | UpdateAttributeRef.t ]
  -> Sil.instr list * Exp.t

(** The translation of an expression can either be a simple expression,
 * or an If expression with an conditional expression and expression for when the
 * condition is true, of false. A simple expression is either an infer Exp, or
 * a Boolean insterted by the frontend *)
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

val map_to_stmts :
  f:(simple_expr -> stmt list) -> orig_node:[< AdaNode.t] -> context -> expr -> stmt list
(** transform an expression to a list of statements by calling f on the leafs *)

val trans_expr : context -> 'a continuation -> [< Expr.t] -> stmt list * 'a
(** Translate an expression to an intermediate representation. *)

val trans_bounds :
  context -> [< Expr.t | DiscreteSubtypeIndication.t] -> stmt list * Sil.instr list * Exp.t * Exp.t

val type_of_expr : context -> [< Expr.t] -> Typ.t
