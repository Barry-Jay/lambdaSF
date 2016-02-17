(**********************************************************************)
(* This program is free software; you can redistribute it and/or      *)
(* modify it under the terms of the GNU Lesser General Public License *)
(* as published by the Free Software Foundation; either version 2.1   *)
(* of the License, or (at your option) any later version.             *)
(*                                                                    *)
(* This program is distributed in the hope that it will be useful,    *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of     *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the      *)
(* GNU General Public License for more details.                       *)
(*                                                                    *)
(* You should have received a copy of the GNU Lesser General Public   *)
(* License along with this program; if not, write to the Free         *)
(* Software Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA *)
(* 02110-1301 USA                                                     *)
(**********************************************************************)


(**********************************************************************)
(*             Intensional Lambda Calculus                            *)
(*                                                                    *)
(* is implemented in Coq by adapting the implementation of            *) 
(* Lambda Calculus from Project Coq                                   *)
(* 2015                                                               *)
(**********************************************************************)

(**********************************************************************)
(*                           Marks.v                                  *)
(*                                                                    *)
(* adapted from Marks.v for Lambda Calculus                           *)
(*                                                                    *)
(*                          Barry Jay                                 *)
(*                                                                    *)
(**********************************************************************)

Require Import Arith.
Require Import Test.
Require Import General.
Require Import Terms.
Require Import Redexes.
Require Import Residuals.

(* Translation from terms to redexes *)

Fixpoint mark (e : lambda) : redexes :=
  match e with
  | Ref i => Var i
  | App M N => Ap false (mark M) (mark N)
  | Abs M => Fun (mark M)
  end. 


(* Reverse translation : erasing the marks *)

Fixpoint unmark (e : redexes) : lambda :=
  match e with
  | Var i => Ref i
  | Ap b U V => App (unmark U) (unmark V)
  | Fun U => Abs (unmark U)
  end.

Lemma inverse : forall M : lambda, M = unmark (mark M).
Proof.
simple induction M; simpl in |- *; trivial; simple induction 1; trivial.
simple induction 1; trivial.
Qed.

Lemma comp_unmark_eq : forall U V : redexes, comp U V -> unmark U = unmark V.
Proof.
simple induction 1; simpl in |- *; trivial; split_all. 
Qed.

(* The converse is true, but not needed in the rest of the development *)

Lemma residuals_mark :
forall M, residuals (mark M) (mark M) (mark M).
Proof. induction M; split_all. Qed.

Hint Resolve residuals_mark.
