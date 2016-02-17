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
(*                LambdaFactor Calculus                               *)
(*                                                                    *)
(* is implemented in Coq by adapting the implementation of            *)
(* Lambda Calculus from Project Coq                                   *)
(* 2015                                                               *)
(**********************************************************************)

(**********************************************************************)
(*                           Eta.v                                    *)
(*                                                                    *)
(*                     Barry Jay                                      *)
(*                                                                    *)
(**********************************************************************)


Require Import Arith.
Require Import Max. 
Require Import Test.
Require Import General. 
Require Import Terms.
Require Import Lambda_tactics.
Require Import Substitution_term.
Require Import Reduction.
Require Import Confluence.


Lemma subst_rec_lift_rec_null2 :
forall V n, subst_rec (lift_rec V (S n) 1) (Ref 0) n = V.
Proof.
simple induction V; split_all. 
unfold insert_Ref. 
unfold relocate. 
elim(test (S n0) n); split_all. 
elim(compare n0 (S n)); split_all.
elim a0; split_all; noway. 
noway. 
elim(compare n0 n); split_all.
elim a; split_all. noway. 
unfold lift; split_all. 
relocate_lt.
subst. replace (n+0) with n by omega; auto. 
Qed. 


Inductive etared1 : termred :=
  | ref_etared : forall i, etared1 (Ref i) (Ref i)
  | app_etared :
      forall M M' ,
      etared1 M M' ->
      forall N N' : lambda, etared1 N N' -> etared1 (App M N) (App M' N')  
  | abs_etared : forall M M' , etared1 M M' -> etared1 (Abs M) (Abs M')
  | eta_red: forall (M M' : lambda),
             etared1 M M' -> 
             etared1 (Abs (App (lift_rec M 0 1) (Ref 0))) M' 
. 

Hint Resolve 
ref_etared app_etared abs_etared    
eta_red
.


Lemma reflective_etared1 : reflective etared1.
Proof. red; induction M; split_all. Qed. 
Hint Resolve reflective_etared1. 

Lemma lift_rec_preserves_etared1 : lift_rec_preserves etared1.
Proof. red. induction 1;  split_all.
relocate_lt. 
rewrite lift_lift_rec; try omega. 
auto. 
Qed. 

Hint Resolve lift_rec_preserves_etared1.



Lemma subst_rec_preserves_etared1 : subst_rec_preserves etared1. 
Proof. 
red. 
intros M M' R; induction R; split_all. 
(* 2 *) 
unfold insert_Ref. elim(compare k i); split_all. elim a; split_all. 
unfold lift. eapply2 lift_rec_preserves_etared1. 
(* 1 *) 
insert_Ref_out. 
rewrite subst_rec_lift_rec1; try omega; split_all.  
Qed. 


Lemma preserves_lift_rec1_etared1 : forall M N : lambda,
   etared1 M N -> forall n, 
      lift_rec (subst_rec M (Ref 0) n) n 1 = M ->
      lift_rec (subst_rec N (Ref 0) n) n 1 = N.
Proof. 
cut(forall p, forall M, p>= rank M -> forall N, etared1 M N -> forall n, 
      lift_rec (subst_rec M (Ref 0) n) n 1 = M ->
      lift_rec (subst_rec N (Ref 0) n) n 1 = N). 
split_all. eapply2 H. 
induction p. 
split_all. 
assert(rank M >0) by eapply2 rank_positive. noway. 
(* p > 0 *) 

induction M; split_all;  inversion H0; subst.
(* 4 *) 
split_all. 
(* 3 *) 
inversion H1. 
simpl. 
assert(lift_rec (subst_rec M' (Ref 0) (S n)) (S n) 1 = M'). 
eapply2 IHM. omega. 
congruence. 
(* 2 *) 
2: simpl; rewrite IHM1; try omega; split_all;   rewrite IHM2; try omega;  split_all. 
(* 1 *) 
unfold rank in *; fold rank in *; rewrite lift_rec_preserves_rank in *. 
inversion H1. 
eapply2 (IHp M0). 
omega. 
rewrite subst_rec_lift_rec1 in H4; try omega.
rewrite lift_lift_rec in H4; try omega.
eapply2 lift_rec_mono. 
Qed. 




(* Diamond Lemmas *) 


Lemma diamond_etared1_etared1 : diamond etared1 etared1. 
Proof.  
red. 
cut(forall p, forall M, p>= rank M -> forall N : lambda,
   etared1 M N ->
   forall P : lambda,
   etared1 M P -> exists Q : lambda, etared1 N Q /\ etared1 P Q). 
split_all. eapply2 H. 
induction p. 
split_all. 
assert(rank M >0) by eapply2 rank_positive. noway. 
(* p > 0 *) 
induction M; split_all; eauto.
(* 3 *) 
inversion H0; inversion H1; exist(Ref n). 
(* 2 *) 
inversion H0; inversion H1; subst.  
(* 5 *)
assert(exists Q, etared1 M' Q /\ etared1 M'0 Q). 
eapply2 IHM. 
omega. 
split_all. 
exist (Abs x). 
(* 4 *) 
subst. 
simpl in *. 
rewrite lift_rec_preserves_rank in *. 
clear H1. 
inversion H3. inversion H7. subst. clear H0 H3 H7. 
assert(lift_rec (subst_rec M'0 (Ref 0) 0) 0 1 = M'0).
eapply2 (preserves_lift_rec1_etared1 (lift_rec M1 0 1)). 
rewrite subst_rec_lift_rec; split_all. 
rewrite lift_rec_null; auto.

assert(etared1 (lift_rec M1 0 1) (lift_rec P 0 1)) by eapply2 lift_rec_preserves_etared1. 
assert(exists Q, etared1 M'0 Q /\ etared1 (lift_rec P 0 1) Q). 
eapply2 IHp. 
rewrite lift_rec_preserves_rank.
omega. 
split_all. 
assert(etared1 (subst_rec (lift_rec P 0 1) (Ref 0) 0) (subst_rec x (Ref 0) 0)). 
eapply2 subst_rec_preserves_etared1. 
rewrite subst_rec_lift_rec in H3; split_all. 
rewrite lift_rec_null in H3.
exist(subst_rec x (Ref 0) 0). 
rewrite <- H0. 
eapply2 eta_red.  
eapply2 subst_rec_preserves_etared1. 
(* 3 *) 
simpl in *. 
rewrite lift_rec_preserves_rank in *. 
clear H0 H1. 
inversion H6. inversion H5. subst. clear H5 H6. 
assert(lift_rec (subst_rec M' (Ref 0) 0) 0 1 = M').
eapply2 (preserves_lift_rec1_etared1 (lift_rec M0 0 1)). 
rewrite subst_rec_lift_rec; split_all. 
rewrite lift_rec_null; auto.

assert(etared1 (lift_rec M0 0 1) (lift_rec N 0 1)) by eapply2 lift_rec_preserves_etared1. 
assert(exists Q, etared1 M' Q /\ etared1 (lift_rec N 0 1) Q). 
eapply2 IHp. 
rewrite lift_rec_preserves_rank.
omega. 
split_all. 
assert(etared1 (subst_rec (lift_rec N 0 1) (Ref 0) 0) (subst_rec x (Ref 0) 0)). 
eapply2 subst_rec_preserves_etared1. 
rewrite subst_rec_lift_rec in H5; split_all. 
rewrite lift_rec_null in H5.
exist(subst_rec x (Ref 0) 0). 
rewrite <- H0. 
eapply2 eta_red.  
eapply2 subst_rec_preserves_etared1. 
(* 2 *) 
simpl in *. 
rewrite lift_rec_preserves_rank in *. 
inversion H5. 
assert (M1 = M0) by eapply2 lift_rec_mono. 
subst. 
eapply2 (IHp M0). 
omega. 
(* 1 *) 
inversion H0; inversion H1. 
assert(exists Q, etared1 M' Q /\ etared1 M'0 Q) by (eapply2 IHM1; omega). 
assert(exists Q, etared1 N' Q /\ etared1 N'0 Q) by (eapply2 IHM2; omega). 
split_all. 
exist(App x0 x). 
Qed. 




Lemma diamond_etared1_par_red1: diamond etared1 par_red1. 
Proof. 
red. 
cut(forall p, forall M, p>= rank M -> forall N : lambda,
   etared1 M N ->
   forall P : lambda,
   par_red1 M P -> exists Q : lambda, par_red1 N Q /\ etared1 P Q).
split_all. eapply2 H. 
induction p. 
split_all. 
assert(rank M >0) by eapply2 rank_positive. noway. 
(* p > 0 *) 
intros M r N R; induction R; split_all; inv par_red1; eauto.
(* 5 *)
assert(p>= rank M0). simpl in *. omega.
assert(p>= rank N). simpl in *. omega. 
assert(exists Q : lambda, par_red1 N' Q /\ etared1 N'0 Q) by eapply2 IHR2.  split_all. 
inversion R1; clear R1.
(* 6 *) 
assert(exists Q : lambda, par_red1 M'1 Q /\ etared1 M'0 Q). eapply2 (IHp M0).  split_all. 
exist (subst x x0). 
unfold subst. eapply2 subst_rec_preserves_etared1. 
(* 5 *)
subst. 
gen3_inv H6 r H H2. 
(* 6 *) 
inversion H8. subst. clear H2 H8. 
gen2_case H H9 M. 
inversion H; subst. clear H. 
elim(preserves_lift_rec_par_red1 (lift_rec l 1 1) M'1 H6 l 1 1); split_all. 
subst. 
unfold subst. 
rewrite subst_rec_lift_rec_null2.
eapply2 (IHp (App (Abs l) N)). 
split_all. 
rewrite lift_rec_preserves_rank in *. 
omega. 
eapply2 beta_red. 
(* 5 *) 
inversion H8. subst. clear H2 H8. 
elim(preserves_lift_rec_par_red1 (lift_rec M 0 1) M'1 H6 M 0 1); split_all. 
subst. 
unfold subst. unfold subst_rec; fold subst_rec. 
rewrite subst_rec_lift_rec; split_all. 
rewrite lift_rec_null. 
insert_Ref_out. 
rewrite lift_rec_null. 
assert(exists Q : lambda, par_red1 M' Q /\ etared1 x0 Q). eapply2 (IHp M). 
rewrite lift_rec_preserves_rank in *. 
omega. 
split_all. 
exist(App x1 x). 
(* 4 *) 
simpl in *. 
assert(exists Q : lambda, par_red1 M' Q /\ etared1 M'0 Q) by (eapply2 IHR1; omega). 
assert(exists Q : lambda, par_red1 N' Q /\ etared1 N'0 Q) by (eapply2 IHR2; omega). 
split_all. 
exist(App x0 x). 
(* 3 *) 
simpl in *. 
assert(exists Q, par_red1 M' Q /\ etared1 M'0 Q) by (eapply2 IHR; omega). 
split_all. 
exist(Abs x). 
(* 2 *) 
assert(p >= rank M).
simpl in *. rewrite lift_rec_preserves_rank in *. omega. 
clear r. 
gen4_case H0 R IHR H M. 
inversion H. subst. 
elim(preserves_lift_rec_par_red1 (lift_rec l 1 1) M'1 H4 l 1 1); split_all. subst. 
clear H4 H IHR . 
unfold subst. 
rewrite subst_rec_lift_rec_null2. 
assert(exists Q : lambda, par_red1 M' Q /\ etared1 (Abs x) Q). 
eapply2 IHp.
simpl; omega. 
split_all. 
exist x0. 
(* 1 *) 
elim(preserves_lift_rec_par_red1 (lift_rec M 0 1) M'1 H4 M 0 1); split_all. subst.
assert(p >= rank M).  
simpl in *.  rewrite lift_rec_preserves_rank in *. omega. 
clear r H4. 
assert(exists Q, par_red1 M' Q /\ etared1 x Q) by (eapply2 IHp). 
split_all. 
exist x0. 
Qed. 



Definition beta_eta1  := sequential par_red1 etared1.
Definition beta_eta := multi_step beta_eta1.

Lemma reflective_beta_eta1: reflective beta_eta1. 
Proof. red; reflect. apply seq_red with M; auto. Qed. 
Hint Resolve reflective_beta_eta1.

Lemma reflective_beta_eta: reflective beta_eta. 
Proof. red; reflect. apply zero_red. Qed. 
Hint Resolve reflective_beta_eta.

Lemma preserves_abs_beta_eta : preserves_abs beta_eta.
Proof. eapply2 preserves_abs_multi_step; eapply2 preserves_abs_seq; red; split_all. Qed.
Hint Resolve  preserves_abs_beta_eta. 

Lemma preserves_app_beta_eta1 : preserves_app beta_eta1.
Proof. eapply2 preserves_app_seq; red; split_all. Qed.
Hint Resolve  preserves_app_beta_eta1. 

Lemma preserves_app_beta_eta : preserves_app beta_eta.
Proof. eapply2 preserves_app_multi_step.  Qed.
Hint Resolve  preserves_app_beta_eta. 

Lemma lift_rec_preserves_beta_eta1 : lift_rec_preserves beta_eta1.
Proof. eapply2 lift_rec_preserves_seq. Qed. 
Hint Resolve lift_rec_preserves_beta_eta1.

Lemma lift_rec_preserves_beta_eta : lift_rec_preserves beta_eta.
Proof. eapply2 lift_rec_preserves_multi_step. Qed.
Hint Resolve lift_rec_preserves_beta_eta. 

Lemma subst_rec_preserves_beta_eta1 : subst_rec_preserves beta_eta1.
Proof. 
eapply2 subst_rec_preserves_seq.
eapply2 subst_rec_preserves_par_red1. 
eapply2 subst_rec_preserves_etared1.
Qed. 
Hint Resolve subst_rec_preserves_beta_eta1.

Lemma subst_rec_preserves_beta_eta : subst_rec_preserves beta_eta.
Proof. eapply2 subst_rec_preserves_multi_step. 
red; split_all;  eapply2 subst_rec_preserves_beta_eta1. 
red; split_all;  eapply2 subst_rec_preserves_beta_eta1. 
Qed.
Hint Resolve subst_rec_preserves_beta_eta. 

Lemma diamond_beta_eta1 : diamond beta_eta1 beta_eta1.
Proof. 
red. split_all. inversion H; subst. inversion H0; subst. 
elim(parallel_moves M N0 H1 N1); split_all. 
elim(diamond_etared1_par_red1 N0 N H2 x); split_all. 
elim(diamond_etared1_par_red1 N1 P H4 x); split_all. 
elim(diamond_etared1_etared1 x x1 H11 x0); split_all. 
exist x2. 
apply seq_red with x0; split_all. 
apply seq_red with x1; split_all. 
Qed. 

Lemma diamond_beta_eta : diamond beta_eta beta_eta.
Proof. eapply2 diamond_tiling. eapply2 diamond_beta_eta1. Qed. 


Theorem confluence_beta_eta:  confluence lambda beta_eta. 
Proof.
red; split_all. eapply2 diamond_beta_eta. Qed. 



Inductive beta_eta_eq : termred := 
| common_reduct : forall M N P, beta_eta M P -> beta_eta N P -> beta_eta_eq M N. 

 
Hint Resolve common_reduct. 

Lemma beta_eta_eq_transitive : forall M N P, beta_eta_eq M N -> beta_eta_eq N P -> beta_eta_eq M P .
Proof. 
split_all. 
inversion H; inversion H0. 
elim(diamond_beta_eta N P0 H2 P1); split_all. 
exist x. 
eapply transitive_red. eexact H1. auto. 
eapply transitive_red. eexact H6. auto. 
Qed. 

Lemma beta_eta_eq_symmetric : forall M N, beta_eta_eq M N -> beta_eta_eq N M.
Proof. split_all. inversion H. eauto. Qed. 

Lemma preserves_abs_beta_eta_eq : Lambda_tactics.preserves_abs beta_eta_eq.
Proof. red. split_all. inversion H. eauto. Qed. 
Hint Resolve  preserves_abs_beta_eta_eq. 

Lemma preserves_app_beta_eta_eq : Lambda_tactics.preserves_app beta_eta_eq.
Proof. red. split_all. inversion H; inversion H0. eauto. Qed. 
Hint Resolve  preserves_app_beta_eta_eq. 


Definition stable (red:termred) M := forall N, red M N -> N = M.

Lemma stable_multi_step : forall red M, stable red M -> stable (multi_step red) M.
Proof. red. split_all. induction H0; split_all. 
assert(N= M) by eapply2 H. subst. 
eapply2 IHmulti_step. 
Qed. 
 
Lemma stable_seq : forall red1 red2 M, stable red1 M -> stable red2 M -> stable (sequential red1 red2) M.
Proof. red. split_all. inversion H1. assert(N0 = M) by auto. subst. auto.  Qed. 
 
Lemma stable_beta_eta_ref: forall n, stable beta_eta (Ref n). 
Proof. split_all. eapply2 stable_multi_step. eapply2 stable_seq. 
red. split_all. inversion H; auto. 
red. split_all. inversion H; auto. 
Qed. 

