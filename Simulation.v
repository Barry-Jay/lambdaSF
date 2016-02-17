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
(*                           Simulation.v                             *)
(*                                                                    *)
(* adapted from Simulation.v for Lambda Calculus                      *)
(*                                                                    *)
(*                          Barry Jay                                 *)
(*                                                                    *)
(**********************************************************************)

(* Reduction of a term by a set of redexes *)

Require Import Arith.
Require Import General.
Require Import Terms.
Require Import Lambda_tactics.
Require Import Reduction.
Require Import Redexes.
Require Import Test.
Require Import Marks.
Require Import Substitution.
Require Import Residuals.

(* Commuting mark and subst *)

Lemma mark_lift_rec :
 forall (M : lamSF) (n k : nat),
 lift_rec_r (mark M) k n = mark (lift_rec M k n).
Proof. simple induction M; split_all. Qed.

Lemma mark_lift :
 forall (M : lamSF) (n : nat), lift_r n (mark M) = mark (lift n M).
Proof.
unfold lift in |- *; unfold lift_r in |- *; intros; apply mark_lift_rec.
Qed.

Lemma mark_subst_rec :
 forall (M N : lamSF) (n : nat),
 subst_rec_r (mark M) (mark N) n = mark (subst_rec M N n).
Proof.
simple induction M; simpl in |- *; split_all.
unfold insert_Var, insert_Ref in |- *.
elim (compare n0 n); split_all. elim a; split_all. 
rewrite (mark_lift N n0); trivial.
Qed.

Lemma mark_subst :
 forall M N : lamSF, subst_r (mark M) (mark N) = mark (subst M N).
Proof.
unfold subst in |- *; unfold subst_r in |- *; intros; apply mark_subst_rec.
Qed.

(* residuals simulates par_red1 *)



Definition simulates (red: termred) := 
  forall M M', red M M' -> exists V, residuals (mark M) V (mark M').


Lemma simulation : forall M M', par_red1 M M' -> exists V, residuals (mark M) V (mark M').
Proof.
induction 1; split_all; eauto. 
unfold subst.
rewrite <- mark_subst_rec.
exist (Ap true (Fun x0) x).
eapply2 Res_redex.
Qed.

(* Commuting unmark and subst *)

Lemma unmark_lift_rec :
 forall (U : redexes) (n k : nat),
 lift_rec (unmark U) k n = unmark (lift_rec_r U k n).
Proof. simple induction U; simpl in |- *; intros; try (case b); split_all. Qed.

Lemma unmark_lift :
 forall (U : redexes) (n : nat), lift n (unmark U) = unmark (lift_r n U).
Proof.
unfold lift in |- *; unfold lift_r in |- *; intros; apply unmark_lift_rec.
Qed.

Lemma unmark_subst_rec :
 forall (U V : redexes) (n : nat),
 subst_rec (unmark U) (unmark V) n = unmark (subst_rec_r U V n).
Proof.
simple induction U; simpl in |- *; split_all.
unfold insert_Var, insert_Ref in |- *.
elim (compare n0 n); split_all. elim a; split_all. 
rewrite (unmark_lift V n0); trivial.
Qed.

Lemma unmark_subst :
 forall U V : redexes, subst (unmark U) (unmark V) = unmark (subst_r U V).
Proof.
unfold subst in |- *; unfold subst_r in |- *; intros; apply unmark_subst_rec.
Qed.

Lemma completeness :
 forall U V W : redexes, residuals U V W -> par_red1 (unmark U) (unmark W).
Proof.
simple induction 1; simpl in |- *; split_all.
replace(unmark (subst_r W2 W1)) with 
(subst (unmark W2) (unmark W1)). 
eapply2 beta_red. 
unfold subst, subst_r; split_all. 
rewrite unmark_subst_rec. auto. 
Qed. 


(**************************************************)
(* Reduction of a lamSF term by a set of redexes   *)
(**************************************************)

Definition reduction (M : lamSF) (U : redexes) (N : lamSF) :=
  residuals (mark M) U (mark N).

Lemma reduction_function :
 forall (M N P : lamSF) (U : redexes),
 reduction M U N -> reduction M U P -> N = P.
Proof.
unfold reduction in |- *; intros; cut (comp (mark N) (mark P)).
intro; rewrite (inverse N); rewrite (inverse P); apply comp_unmark_eq;
 trivial.
apply mutual_residuals_comp with U (mark M) (mark M); trivial.
Qed.