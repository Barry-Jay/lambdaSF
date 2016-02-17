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
(*               Intensional Lambda Calculus                          *)
(*                                                                    *)
(* is implemented in Coq by adapting the implementation               *) 
(* of Lambda Calculus  from Project Coq                               *)
(* 2015                                                               *)
(**********************************************************************)

(**********************************************************************)
(*                   LamSF_Normal.v                                   *)
(*                                                                    *)
(*                      Barry Jay                                     *)
(*                                                                    *)
(**********************************************************************)

Require Import Arith.
Require Import General.
Require Import Max. 
Require Import Test.
Require Import LamSF_Terms.
Require Import LamSF_Tactics.
Require Import LamSF_Substitution_term.
Require Import SF_reduction.
Require Import LamSF_reduction.


(* normal terms *) 

Inductive normal : lamSF -> Prop := 
| nf_ref : forall n, normal (Ref n)
| nf_op : forall o, normal (Op o)
| nf_abs : forall M, normal M -> normal (Abs M)
| nf_active : forall M1 M2, normal M1 -> normal M2 -> 
                              status (App M1 M2) >0 -> normal (App M1 M2)  
| nf_compound : forall M1 M2, normal M1 -> normal M2 -> 
                              compound (App M1 M2) -> normal (App M1 M2)  
.

Hint Resolve nf_ref nf_op nf_active nf_compound nf_abs. 


Lemma lift_rec_preserves_normal :
forall M, normal M  -> forall n k, normal(lift_rec M n k).
Proof. 
intros M nor; induction nor; split_all.
eapply2 nf_active.
2: gen2_inv nor1 IHnor1 H. 
assert(status (lift_rec (App M1 M2) n k) = relocate(status (App M1 M2)) (S n) k). 
eapply2 lift_rec_preserves_status. 
unfold lift_rec in H0; fold lift_rec in H0. 
rewrite H0. 
unfold relocate. 
elim(test (S n) (status (App M1 M2))); split_all; omega.  
Qed. 


Lemma not_active_factorable : 
forall M, normal M -> status M = 0 -> 
(exists o, M = Op o) \/ compound M.
Proof. 
intros M nor; induction nor; split_all. 
left; eauto. 
assert(status M = 0 \/ status M = 1) by omega. 
inversion H0. 
elim IHnor; split_all. subst. right; auto. 
right. 
eapply2 abs_active_compound. 
simpl in *. noway. 
Qed. 


Lemma normal_star :  forall M, normal M -> normal (star M). 
Proof.  
intros M nor; induction nor; split_all; unfold_op; split_all. 
case n; split_all. 
Qed.

Lemma normal_component_l : forall M, normal M -> normal (left_component M). 
Proof.  intros M nor; induction nor; split_all; unfold_op; split_all. Qed.
Lemma normal_component_r : forall M, normal M -> normal (right_component M). 
Proof.  intros M nor; induction nor; split_all; unfold_op; split_all. 
repeat(eapply2 nf_compound). 
eapply2 normal_star. 
Qed.

Definition irreducible M (red:termred) := forall N, red M N -> False. 

Lemma ref_irreducible : forall n, irreducible (Ref n) lamSF_red1. 
Proof. intro n. red. split_all. inversion H; auto. Qed. 

Lemma active_irreducible : forall M, status M >0 ->  irreducible (left_component M) lamSF_red1 ->  irreducible (right_component M) lamSF_red1 -> irreducible M lamSF_red1. 
Proof. 
intros M s l r.  red. split_all. 
gen3_inv s l r H; try noway.  
(* 4 *) 
eapply2 l.
(* 3 *) 
eapply2 r. 
(* 2 *) 
assert(lamSF_red1 (star M0) (star M')). 
eapply2 lamSF_red1_preserves_star_active. omega. 
eapply2 r. 
(* 1 *) 
assert(status P = 0) by eapply2 compound_not_active; noway. 
Qed. 



Lemma compound_irreducible : forall M, compound M ->  irreducible (left_component M) lamSF_red1 ->  irreducible (right_component M) lamSF_red1 -> irreducible M lamSF_red1. 
Proof. 
intros M c l r.  red. split_all. 
gen3_case l r H c; inversion H; split_all. 
(* 11 *) 
inversion H3. 
(* 10 *) 
inversion H. inversion H7. eapply2 r. 
(* 9 *)
eapply2 l. 
(* 8 *) 
eapply2 r. 
(* 7 *) 
inversion H1. 
(* 6 *)
inversion H0. subst; simpl in *; split_all. 
inversion H3. inversion H5. 
eapply2 r. 
(* 5 *) 
subst; simpl in *. 
inversion H0. inversion H2. eapply2 r. 
subst. eapply2 r. 
(* 4 *) 
subst; simpl in *. 
inversion H0. inversion H2. inversion H5. 
(* 3 *) 
subst; simpl in *. 
inversion H0. 
inversion H3. 
assert(lamSF_red1 (Abs (star M1)) (Abs (star M'0))). 
eapply2 abs_lamSF_red. 
eapply2 lamSF_red1_preserves_star_compound. 
eapply r. eexact H8. 
(* 2 *) 
subst; simpl in *. 
inversion H0.
inversion H3. 
assert(lamSF_red1 (Abs (star M1))(Abs (star M'0))). 
eapply2 abs_lamSF_red. 
eapply2 lamSF_red1_preserves_star_active. omega. 
eapply r. eexact H8. 
(* 1 *) 
subst; simpl in *. 
inversion H0.
assert(lamSF_red1  (star M0)(star M')). 
eapply2 lamSF_red1_preserves_star_active. omega. 
eapply r. eexact H5. 
Qed. 

Lemma abs_irreducible : 
forall M, irreducible M lamSF_red1 ->  irreducible (Abs M) lamSF_red1. 
Proof. red; split_all. inversion H0. eapply2 H. Qed. 



Lemma normal_is_irreducible: 
forall M, normal M -> irreducible M lamSF_red1. 
Proof. 
intros M nor; induction nor; split_all.  
eapply2 ref_irreducible. 
red; split_all. inversion H. 
eapply2 abs_irreducible.
eapply2 active_irreducible.  
eapply2 compound_irreducible. 
Qed. 



(* 
The basic progress result, that all irreducible terms are normal.
 *) 

Theorem progress : 
forall (M : lamSF), normal M \/ (exists N, lamSF_red1 M N) .
Proof. 
induction M; try (inversion IHM); subst; split_all; eauto.
elim IHM1; elim IHM2; split_all; eauto. 
inversion H0; subst; eauto. 
(* 3 *) 
left; eapply2 nf_active. split_all. omega. 
(* 2 *) 
left; eapply2 nf_active. simpl in *. split_all. 
gen_case H3 M0. gen_case H3 l; noway. 
(* 1 *) 
gen2_inv H1 H2 H3; subst. 
inversion H1; subst; split_all.  
inversion H8; subst; split_all. 
clear IHM2 H1 H3 IHM1 H0 H6 H8.
case o; split_all. 
right; eauto. 
inversion H7; subst; split_all. 
(* 4 *)
left; split_all. eapply2 nf_active. split_all. omega. 
(* 3 *) 
right; eauto. 
(* 2 *) 
2: right; eauto. 
(* 1 *) 
assert(status M0 = 0 \/ status M0 = 1 \/ status M0 >1) by omega. 
inversion H1. 
elim (not_active_factorable  M0); split_all; subst; split_all.
(* 3 *) 
right; eauto.
inversion H3; subst; right; eauto. 
(* 1 *) 
inversion H2.
assert(M0 = Ref 0 \/ M0 <> Ref 0) by eapply2 decidable_term_equality. 
inversion H4; subst. 
right; eauto. 
assert(compound (Abs M0)) . eapply2 abs_active_compound.  
right; eauto. 
left; eauto. 
eapply2 nf_active. 
split_all. 
omega. 
Qed. 


Lemma irreducible_is_normal: 
forall M, irreducible M lamSF_red1 -> normal M. 
Proof. split_all. elim(progress M); split_all. assert False by eapply2 H; noway. Qed. 

Theorem irreducible_iff_normal: forall M, irreducible M lamSF_red1 <-> normal M. 
Proof. split_all. eapply2 irreducible_is_normal. eapply2 normal_is_irreducible. Qed. 




Lemma normal_is_stable: forall M, normal M -> forall N, lamSF_red M N -> N = M.
Proof. 
split_all. 
inversion H0; inv1 lamSF_red. 
assert False by eapply2 normal_is_irreducible. noway. 
Qed. 

Lemma unf: forall M N P, lamSF_red M N -> lamSF_red M P -> normal N -> normal P -> N = P.
Proof.  
split_all. 
elim(diamond_lamSF_red M N H P); split_all. 
assert (x=N) by eapply2 normal_is_stable. 
assert (x=P) by eapply2 normal_is_stable. congruence. 
Qed. 

