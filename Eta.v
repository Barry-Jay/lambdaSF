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
Require Import LamSF_Terms.
Require Import LamSF_Substitution_term.
Require Import LamSF_Tactics.
Require Import Beta_Reduction.
Require Import LamSF_Confluence.
Require Import SF_reduction.
Require Import LamSF_reduction.
Require Import LamSF_Normal.
Require Import LamSF_Closed.
Require Import LamSF_Eval.
Require Import Equal.



Inductive beta_eta_eq : termred :=
  | ref_etared : forall i, beta_eta_eq (Ref i) (Ref i)
  | op_etared : forall o, beta_eta_eq (Op o) (Op o)
  | app_etared :
      forall M M' ,
      beta_eta_eq M M' ->
      forall N N' : lamSF, beta_eta_eq N N' -> beta_eta_eq (App M N) (App M' N')  
  | abs_etared : forall M M' , beta_eta_eq M M' -> beta_eta_eq (Abs M) (Abs M')
  | beta_red: forall (M M' N N': lamSF),
             beta_eta_eq M M' -> beta_eta_eq N N' ->  
             beta_eta_eq (App (Abs M) N) (subst N' M')
  | eta_red: forall (M M' : lamSF),
             beta_eta_eq M M' -> 
             beta_eta_eq (Abs (App (lift_rec M 0 1) (Ref 0))) M' 
  | s_etared: forall (M M' N N' P P' : lamSF),
             beta_eta_eq M M' -> beta_eta_eq N N' -> beta_eta_eq P P' ->                  
             beta_eta_eq 
                   (App (App (App s_op M) N) P) 
                  (App (App M' P') (App N' P'))
  | k_etared : forall M  M' N o,  beta_eta_eq M M' -> 
               beta_eta_eq (App (App (App f_op (Op o)) M) N) M' 
  | symm_etared : forall M M', beta_eta_eq M M' -> beta_eta_eq M' M
  | trans_etared : forall M N P, beta_eta_eq M N -> beta_eta_eq N P -> beta_eta_eq M P
.

Hint Resolve 
ref_etared op_etared app_etared abs_etared    
beta_red eta_red s_etared k_etared symm_etared trans_etared
.

Lemma reflective_beta_eta_eq : reflective beta_eta_eq.
Proof. red; induction M; split_all. Qed. 
Hint Resolve reflective_beta_eta_eq. 

Lemma preserves_abs_beta_eta_eq : preserves_abs beta_eta_eq.
Proof. red. split_all.  Qed. 
Hint Resolve  preserves_abs_beta_eta_eq. 

Lemma preserves_app_beta_eta_eq : preserves_app beta_eta_eq.
Proof. red. split_all.  Qed. 
Hint Resolve  preserves_app_beta_eta_eq. 


Definition stable (red:termred) M := forall N, red M N -> N = M.

Lemma stable_multi_step : forall red M, stable red M -> stable (multi_step red) M.
Proof. red. split_all. induction H0; split_all. 
assert(N= M) by eapply2 H. subst. 
eapply2 IHmulti_step. 
Qed. 
 
Lemma stable_seq : forall red1 red2 M, stable red1 M -> stable red2 M -> stable (sequential red1 red2) M.
Proof. red. split_all. inversion H1. assert(N0 = M) by auto. subst. auto.  Qed. 
 

Definition ref := Ref. 
Definition ap := App . 
Definition abs := Abs. 
Definition abs_S := (abs (abs (abs (ap (ap (ref 2) (ref 0)) (ap (ref 1) (ref 0)))))) . 
Definition abs_K := (abs (abs (ref 1))).
Definition abs_I := (abs (ref 0)).
Definition abs_KI := (abs (abs (ref 0))).


Lemma eq_I : beta_eta_eq i_op abs_I.
Proof. 
split_all. 
assert(beta_eta_eq  (abs (ap i_op (ref 0))) i_op). 
unfold abs, ap; auto. 
assert (lift_rec i_op 0 1 = i_op).  unfold_op; split_all. 
rewrite <- H at 1. 
eapply2 eta_red.
assert(beta_eta_eq (abs (ap i_op (ref 0))) abs_I).
unfold abs_I. 
repeat (eapply2 preserves_abs_beta_eta_eq). 
unfold_op; unfold ap.  
apply trans_etared with (App (App k_op (ref 0))(App k_op (ref 0))); split_all. 
unfold_op; unfold ap.  split_all. 
eauto. 
Qed. 

Lemma eq_K : beta_eta_eq k_op abs_K.
Proof. 
split_all. 
assert(k_op = lift_rec k_op 0 1) by auto. 
assert(beta_eta_eq  k_op (abs (ap k_op (ref 0)))). 
rewrite H at 2. auto. 
assert(ap k_op (ref 1) = lift_rec (ap k_op (ref 0)) 0 1) by auto. 
assert(beta_eta_eq   (abs (ap k_op (ref 0))) (abs (abs (ap (ap k_op (ref 1)) (ref 0))))). 
rewrite H1. auto. 
assert(beta_eta_eq (abs (abs (ap (ap k_op (ref 1)) (ref 0)))) (abs (abs (ref 1)))).
eapply2 abs_etared. eapply2 abs_etared. 
unfold ap, ref; unfold_op. auto. 
eauto. 
Qed. 

Lemma eq_S : beta_eta_eq s_op abs_S.
Proof. 
split_all. 
assert(s_op = lift_rec s_op 0 1) by auto. 
assert(beta_eta_eq  s_op (abs (ap s_op (ref 0)))). 
rewrite H at 2. auto. 
assert(ap s_op (ref 1) = lift_rec (ap s_op (ref 0)) 0 1) by auto. 
assert(beta_eta_eq   (abs (ap s_op (ref 0))) (abs (abs (ap (ap s_op (ref 1)) (ref 0))))). 
rewrite H1. auto. 
assert(ap (ap s_op (ref 2))(ref 1) = lift_rec (ap (ap s_op (ref 1)) (ref 0)) 0 1) by auto. 
assert(beta_eta_eq (abs (abs (ap (ap s_op (ref 1)) (ref 0)))) (abs (abs (abs (ap (ap (ap s_op (ref 2)) (ref 1)) (ref 0)))))). 
rewrite H3. auto. 
assert(beta_eta_eq (abs (abs (abs (ap (ap (ap s_op (ref 2)) (ref 1)) (ref 0))))) abs_S). 
unfold abs_S. 
eapply2 abs_etared. eauto. 
Qed. 



Lemma star_equiv_abs : forall M, beta_eta_eq (star M) (Abs M) . 
Proof. 
induction M; split_all. 
(* 3 *)  
case n; split_all. eapply2 eq_I. 
(* 4 *) 
apply trans_etared with (abs (ap (lift_rec (ap k_op (Ref n0)) 0 1) (ref 0))). auto. 
(* 3 *)
simpl. eapply2 abs_etared. relocate_lt. auto. 
(* 2 *) 
apply trans_etared with (abs (ap (lift_rec (ap k_op (Op o)) 0 1) (ref 0))). auto. 
simpl. 
eapply2 abs_etared.
(* 1 *) 
apply trans_etared with (abs (ap (lift_rec (ap (ap s_op (Abs M1)) (Abs M2)) 0 1) (ref 0))). auto. 
eapply2 abs_etared. simpl. 
apply trans_etared with (ap (ap  (Abs (lift_rec M1 1 1)) (ref 0)) (ap (Abs (lift_rec M2 1 1)) (ref 0))). 
auto. 
eapply2 app_etared. simpl. 
apply trans_etared with (subst (ref 0) (lift_rec M1 1 1)). auto. 
unfold subst. rewrite subst_rec_lift_rec2. auto. 
apply trans_etared with (subst (ref 0) (lift_rec M2 1 1)). auto. 
unfold subst. rewrite subst_rec_lift_rec2. auto. 
Qed. 

