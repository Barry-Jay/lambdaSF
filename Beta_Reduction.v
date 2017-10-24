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
(*                 Intensional Lambda Calculus                        *)
(*                                                                    *)
(* is implemented in Coq by adapting the implementation of            *) 
(* Lambda Calculus from Project Coq                                   *) 
(* 2015                                                               *)
(**********************************************************************)
(**********************************************************************)
(*                        LamSF_Reduction.v                           *)
(*                                                                    *)
(* adapted from Reduction.v for Lambda Calculus                       *)
(*                                                                    *)
(*                          Barry Jay                                 *)
(*                                                                    *)
(**********************************************************************)

Require Import Arith.
Require Import General.
Require Import Test.
Require Import LamSF_Terms.
Require Import LamSF_Tactics.
Require Import LamSF_Substitution_term.
Require Import Omega.

(* Parallel beta reduction *)

Inductive par_red1: termred := 
  | beta_red : forall M M' N N', par_red1 M M' -> par_red1 N N' -> 
                  par_red1 (App (Abs M) N) (subst N' M')
  | ref_par_red : forall i, par_red1 (Ref i) (Ref i)
  | op_par_red : forall o, par_red1 (Op o) (Op o)
  | app_par_red :
      forall M M' ,
      par_red1 M M' ->
      forall N N' : lamSF, par_red1 N N' -> par_red1 (App M N) (App M' N')
  | abs_par_red :
      forall M M', par_red1 M M' -> par_red1 (Abs M) (Abs M') 
.

Hint Resolve beta_red ref_par_red op_par_red abs_par_red app_par_red . 

Definition par_red := multi_step par_red1. 

Lemma refl_par_red1: reflective par_red1. 
Proof. red; induction M; split_all.  Qed. 
Hint Resolve refl_par_red1. 

Lemma lift_rec_preserves_par_red1 :  lift_rec_preserves par_red1.
Proof. red. induction 1; split_all;
unfold subst.  
assert(n=0+n) by omega. rewrite H1 at 3. 
rewrite lift_rec_subst_rec; split_all.  eapply2 beta_red. 
Qed. 

Hint Resolve lift_rec_preserves_par_red1. 

Lemma lift_rec_preserves_par_red :   lift_rec_preserves par_red.
Proof. red; eapply2 lift_rec_preserves_multi_step.  Qed.

Lemma subst_rec_preserves_par_red1 : subst_rec_preserves par_red1.
Proof. red.  induction 1; split_all; try (case b); split_all. 
unfold subst. split_all. 
assert (k = 0+k) by omega. rewrite H2 at 3.  
rewrite subst_rec_subst_rec. eapply2 beta_red.  

unfold insert_Ref. elim(compare k i); split_all. 
elim a; split_all.  
unfold lift. auto.
Qed. 


Lemma preserves_lift_rec_par_red1 : preserves_lift_rec par_red1.
Proof. red.  intros M N PR; induction PR; split_all; inv_lift_rec; eauto.
eelim IHPR1; eelim IHPR2; split_all; clear IHPR1 IHPR2. subst. 
exist(subst x x0). 
unfold subst. 
simpl. 
replace n with (0+n) by omega. 
rewrite lift_rec_subst_rec. 
split_all. 

eelim IHPR1; eelim IHPR2; split_all. subst.
exist(App x0 x).

inversion H. subst. 
eelim IHPR; split_all. subst. 
exist(Abs x).
Qed. 

Lemma par_red1_preserves_lift1 : 
forall M N, par_red1 M N -> forall M0, (lift 1 M0) = M -> exists N0, par_red1 M0 N0 /\ lift 1 N0 = N. 
Proof. split_all. unfold lift in *. eapply2 preserves_lift_rec_par_red1. Qed.
