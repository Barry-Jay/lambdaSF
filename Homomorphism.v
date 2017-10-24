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
(*                   Homomorphism.v                                   *)
(*                                                                    *)
(*                     Barry Jay                                      *)
(*                                                                    *)
(**********************************************************************)


Require Import Arith.
Require Import Max. 
Require Import Test.
Require Import General. 
Require Import Lambda.Terms.
Require Import Lambda.Lambda_tactics.
Require Import Lambda.Substitution_term.
Require Import Lambda.Reduction.
Require Import Lambda.Redexes.
Require Import Lambda.Substitution.
Require Import Lambda.Residuals.
Require Import Lambda.Marks.
Require Import Lambda.Simulation.
Require Import Lambda.Cube.
Require Import Lambda.Confluence.
Require Import Lambda.Eta.
Require Import Lambda.Closed.
Require Import LamSF_Terms.
Require Import LamSF_Tactics.
Require Import LamSF_Substitution_term.
Require Import SF_reduction.
Require Import LamSF_reduction.
Require Import LamSF_Normal.
Require Import LamSF_Closed.
Require Import LamSF_Eval.
Require Import Omega.

Definition ref := Terms.Ref. 
Definition ap := Terms.App . 
Definition abs := Terms.Abs. 
Definition abs_S := (abs (abs (abs (ap (ap (ref 2) (ref 0)) (ap (ref 1) (ref 0)))))) . 
Definition abs_K := (abs (abs (ref 1))).
Definition abs_I := (abs (ref 0)).
Definition abs_KI := (abs (abs (ref 0))).


Inductive homomorphism: (lamSF -> lambda) -> Prop := 
| hom : forall h : lamSF -> lambda, 
  (forall M N, h (App M N) = Terms.App (h M) (h N)) -> 
  (forall n, h(Ref n) = Terms.Ref n) -> 
  (forall M N, lamSF_red M N -> beta_eta_eq (h M) (h N)) -> 
   (forall M, maxvar M = 0 -> Closed.maxvar (h M) = 0 ) -> 
homomorphism h 
.

Lemma homomorphism_I : forall h, homomorphism h -> beta_eta_eq (h i_op) abs_I.
Proof. 
split_all. 
inversion_clear H; split_all. 
assert(Closed.maxvar(h i_op) = 0) by eapply2 H3. 
assert(forall k, Terms.lift_rec (h i_op) 0 k = h i_op). 
eapply2 Closed.lift_rec_closed. omega. 

assert(beta_eta  (abs (ap (h i_op) (ref 0))) (h i_op)). 
unfold beta_eta; Lambda_tactics.one_step. 
apply Lambda_tactics.seq_red with  (abs (ap (h i_op) (ref 0))); auto. 
unfold abs, ap; auto. 
rewrite <- (H4 1) at 1. 
auto. 


assert(beta_eta
         (abs (ap (h i_op) (ref 0)))
         (abs (h (App i_op (Ref 0))))). 
repeat (eapply2 preserves_abs_beta_eta). 
repeat (rewrite <- H1). 
repeat (rewrite <- H0). 
eapply2 Lambda_tactics.zero_red. 

(* end step 2 *) 

elim(diamond_beta_eta  (abs (ap (h i_op) (ref 0)))
         (h i_op) H5 (abs (h (App i_op (Ref 0))))); split_all. 
assert(beta_eta_eq  (h i_op)
            (abs (h (App i_op (Ref 0))))). 
eapply2 common_reduct. 

(* end step 3 *) 

assert(beta_eta_eq  
            (abs (h (App i_op (Ref 0))))
 abs_I). 
unfold abs_I. 
repeat (eapply2 preserves_abs_beta_eta_eq). 
apply beta_eta_eq_transitive with (h (App (App k_op (Ref 0)) (App k_op (Ref 0)))).
eapply2 H2. 
unfold_op; auto. 
apply beta_eta_eq_transitive with (h (Ref 0)).
eapply2 H2. 
unfold_op; auto. 
repeat (rewrite H0); repeat (rewrite H1). 
unfold ap, ref; eauto.  
eapply2 beta_eta_eq_transitive; eauto. 
Qed. 

Lemma homomorphism_K : forall h, homomorphism h -> beta_eta_eq (h k_op) abs_K.
Proof. 
split_all. 
inversion_clear H; split_all. 
assert(Closed.maxvar(h k_op) = 0) by eapply2 H3. 
assert(forall k, Terms.lift_rec (h k_op) 0 k = h k_op). 
eapply2 Closed.lift_rec_closed. omega. 

assert(beta_eta  (abs (abs (ap (ap (h k_op) (ref 1)) (ref 0)))) (h k_op)). 
apply Lambda_tactics.succ_red with (abs (ap (h k_op) (ref 0))). 
unfold beta_eta1. 
apply Lambda_tactics.seq_red with (abs (abs (ap (ap (h k_op) (ref 1)) (ref 0)))).
auto. 
unfold abs, ap; auto. 
eapply2 abs_etared. 
replace (Terms.App (h k_op)(ref 1)) with (Terms.lift_rec (ap (h k_op) (ref 0)) 0 1).
eapply2 eta_red.  
 (unfold abs, ap); split_all. 
Lambda_tactics.relocate_lt. 
rewrite H4. 
auto. 

Lambda_tactics.one_step. 
apply Lambda_tactics.seq_red with  (abs (ap (h k_op) (ref 0))); auto. 
unfold abs, ap; auto. 
rewrite <- (H4 1) at 1. 
auto. 


assert(beta_eta
         (abs (abs (ap (ap (h k_op) (ref 1)) (ref 0))))
         (abs (abs (h (App (App k_op (Ref 1)) (Ref 0)))))). 
repeat (eapply2 preserves_abs_beta_eta). 
repeat (rewrite <- H1). 
repeat (rewrite <- H0). 
eapply2 Lambda_tactics.zero_red. 

(* end step 2 *) 

elim(diamond_beta_eta  (abs (abs (ap (ap (h k_op) (ref 1)) (ref 0))))
         (h k_op) H5 
            (abs (abs (h (App (App k_op  (Ref 1)) (Ref 0)))))); split_all. 
assert(beta_eta_eq  (h k_op)
            (abs (abs (h (App (App k_op (Ref 1)) (Ref 0)))))). 
eapply2 common_reduct. 

(* end step 3 *) 

assert(beta_eta_eq  
            (abs (abs (h (App (App k_op (Ref 1)) (Ref 0)))))
 abs_K). 
unfold abs_K. 
repeat (eapply2 preserves_abs_beta_eta_eq). 
apply beta_eta_eq_transitive with (h (Ref 1)).
eapply2 H2. 
unfold_op; auto. 
repeat (rewrite H0); repeat (rewrite H1). 
unfold ap, ref; eauto.  
eapply2 beta_eta_eq_transitive; eauto. 
Qed. 


Lemma homomorphism_KI : forall h, homomorphism h -> beta_eta_eq (h (App k_op i_op)) abs_KI.
Proof. 
split_all. 
inversion_clear H; split_all. 
assert(Closed.maxvar(h  (App k_op i_op)) = 0) by eapply2 H3. 
assert(forall k, Terms.lift_rec (h (App k_op i_op)) 0 k = h (App k_op i_op)). 
eapply2 Closed.lift_rec_closed. omega. 

assert(beta_eta  (abs (abs (ap (ap (h (App k_op i_op)) (ref 1)) (ref 0)))) (h (App k_op i_op))). 
apply Lambda_tactics.succ_red with (abs (ap (h (App k_op i_op)) (ref 0))). 
unfold beta_eta1. 
apply Lambda_tactics.seq_red with (abs (abs (ap (ap (h (App k_op i_op)) (ref 1)) (ref 0)))).
auto. 
unfold abs, ap; auto. 
eapply2 abs_etared. 
replace (Terms.App (h (App k_op i_op))(ref 1)) with (Terms.lift_rec (ap (h (App k_op i_op)) (ref 0)) 0 1).
eapply2 eta_red.  
 (unfold abs, ap); split_all. 
Lambda_tactics.relocate_lt. 
rewrite H4. 
auto. 

Lambda_tactics.one_step. 
apply Lambda_tactics.seq_red with  (abs (ap (h (App k_op i_op)) (ref 0))); auto. 
unfold abs, ap; auto. 
rewrite <- (H4 1) at 1. 
auto. 


assert(beta_eta
         (abs (abs (ap (ap (h (App k_op i_op)) (ref 1)) (ref 0))))
         (abs (abs (h (App (App (App k_op i_op) (Ref 1)) (Ref 0)))))). 
repeat (eapply2 preserves_abs_beta_eta). 
repeat (rewrite <- H1). 
repeat (rewrite <- H0). 
eapply2 Lambda_tactics.zero_red. 

(* end step 2 *) 

elim(diamond_beta_eta  (abs (abs (ap (ap (h (App k_op i_op)) (ref 1)) (ref 0))))
         (h (App k_op i_op)) H5 
            (abs (abs (h (App (App (App k_op i_op)  (Ref 1)) (Ref 0)))))); split_all. 
assert(beta_eta_eq  (h (App k_op i_op))
            (abs (abs (h (App (App (App k_op i_op) (Ref 1)) (Ref 0)))))). 
eapply2 common_reduct. 

(* end step 3 *) 

assert(beta_eta_eq  
            (abs (abs (h (App (App (App k_op i_op) (Ref 1)) (Ref 0)))))
 abs_KI). 
unfold abs_KI. 
repeat (eapply2 preserves_abs_beta_eta_eq). 
apply beta_eta_eq_transitive with (h (App i_op (Ref 0))).
eapply2 H2. 
unfold_op; auto. 
apply beta_eta_eq_transitive with (h (App (App k_op (Ref 0)) (App k_op (Ref 0)))).
eapply2 H2. 
unfold_op; auto. 
apply beta_eta_eq_transitive with (h (Ref 0)).
eapply2 H2. 
unfold_op; auto. 
repeat (rewrite H0); repeat (rewrite H1). 
unfold ap, ref; eauto.  
eapply2 beta_eta_eq_transitive; eauto. 
Qed. 





Lemma homomorphism_S : forall h, homomorphism h -> beta_eta_eq (h (Op Sop)) abs_S.
Proof. 
split_all. 
inversion_clear H; split_all. 
assert(Closed.maxvar(h (Op Sop)) = 0) by eapply2 H3. 
assert(forall k, Terms.lift_rec (h (Op Sop)) 0 k = h (Op Sop)). 
eapply2 Closed.lift_rec_closed. omega. 

assert(beta_eta  (abs (abs (abs (ap (ap (ap (h (Op Sop)) (ref 2)) (ref 1)) (ref 0))))) (h (Op Sop))). 
apply Lambda_tactics.succ_red with (abs (abs (ap (ap (h (Op Sop)) (ref 1)) (ref 0)))). 
unfold beta_eta1. 
apply Lambda_tactics.seq_red with (abs (abs (abs (ap (ap (ap (h (Op Sop)) (ref 2)) (ref 1)) (ref 0))))).
auto. 
unfold abs, ap; auto. 
eapply2 abs_etared. eapply2 abs_etared. 
replace (Terms.App (Terms.App (h (Op Sop)) (ref 2)) (ref 1)) with (Terms.lift_rec (ap (ap (h (Op Sop)) (ref 1)) (ref 0)) 0 1).
eapply2 eta_red.  
 (unfold abs, ap); split_all. 
Lambda_tactics.relocate_lt. 
rewrite H4. 
auto. 

apply Lambda_tactics.succ_red with (abs (ap (h (Op Sop)) (ref 0))). 
unfold beta_eta1. 
apply Lambda_tactics.seq_red with (abs (abs (ap (ap (h (Op Sop)) (ref 1)) (ref 0)))).
auto. 
unfold abs, ap; auto. 
eapply2 abs_etared. 
replace (Terms.App (h (Op Sop))(ref 1)) with (Terms.lift_rec (ap (h (Op Sop)) (ref 0)) 0 1).
eapply2 eta_red.  
 (unfold abs, ap); split_all. 
Lambda_tactics.relocate_lt. 
rewrite H4. 
auto. 

Lambda_tactics.one_step. 
apply Lambda_tactics.seq_red with  (abs (ap (h (Op Sop)) (ref 0))); auto. 
unfold abs, ap; auto. 
rewrite <- (H4 1) at 1. 
auto. 

(* end step 1 *) 

assert(beta_eta
         (abs (abs (abs (ap (ap (ap (h (Op Sop)) (ref 2)) (ref 1)) (ref 0)))))
         (abs (abs (abs (h (App (App (App (Op Sop) (Ref 2)) (Ref 1)) (Ref 0))))))). 
repeat (eapply2 preserves_abs_beta_eta). 
repeat (rewrite <- H1). 
repeat (rewrite <- H0). 
eapply2 Lambda_tactics.zero_red. 

(* end step 2 *) 

elim(diamond_beta_eta  (abs (abs (abs (ap (ap (ap (h (Op Sop)) (ref 2)) (ref 1)) (ref 0)))))
         (h (Op Sop)) H5 (abs
            (abs (abs (h (App (App (App (Op Sop) (Ref 2)) (Ref 1)) (Ref 0))))))); split_all. 
assert(beta_eta_eq  (h (Op Sop)) (abs
            (abs (abs (h (App (App (App (Op Sop) (Ref 2)) (Ref 1)) (Ref 0))))))). 
eapply2 common_reduct. 

(* end step 3 *) 

assert(beta_eta_eq  (abs
            (abs (abs (h (App (App (App (Op Sop) (Ref 2)) (Ref 1)) (Ref 0))))))
 abs_S). 
unfold abs_S. 
repeat (eapply2 preserves_abs_beta_eta_eq). 
apply beta_eta_eq_transitive with (h (App (App (Ref 2) (Ref 0)) (App (Ref 1) (Ref 0)))). 
eapply2 H2. 
repeat (rewrite H0); repeat (rewrite H1). 
unfold ap, ref; eauto.  
eapply2 beta_eta_eq_transitive; eauto. 
Qed. 

Lemma identity_M: forall h, homomorphism h -> forall M, beta_eta_eq (ap (ap (h s_op) (h k_op)) (h M)) abs_I. 
Proof. 
split_all. 
assert(beta_eta_eq (h (Op Sop)) abs_S) by (eapply2 homomorphism_S). 
assert(beta_eta_eq (h k_op) abs_K) by (eapply2 homomorphism_K). 
assert(beta_eta_eq (ap (ap (h s_op) (h k_op)) (h M)) (ap (ap abs_S abs_K) (h M))). 
repeat (eapply2 preserves_app_beta_eta_eq). 
assert(beta_eta (ap (ap abs_S abs_K) (h M)) abs_I). 
unfold abs_S, abs_I, ap, abs, par_red.
apply Lambda_tactics.succ_red with (ap (Terms.subst abs_K (abs (abs (ap (ap (ref 2) (ref 0)) (ap (ref 1) (ref 0)))))) (h M)). 
unfold beta_eta1. Lambda_tactics.seq_l. 
unfold Terms.subst. 
unfold abs_K, ap, abs, ref, Terms.subst_rec; fold Terms.subst_rec. 
Lambda_tactics.insert_Ref_out. 
Lambda_tactics.relocate_lt. 
apply Lambda_tactics.succ_red with (Terms.subst (h M) (abs (ap (ap (abs (abs (ref 1))) (ref 0))(ap (ref 1) (ref 0))))). 
unfold beta_eta1. Lambda_tactics.seq_l. 
unfold Terms.subst. 
unfold abs_K, ap, abs, ref, Terms.subst_rec; fold Terms.subst_rec. 
Lambda_tactics.insert_Ref_out. 
apply Lambda_tactics.succ_red with (abs (ap (Terms.subst (ref 0) (abs (ref 1))) (ap  (Terms.lift_rec (h M) 0 1) (ref 0)))). 
unfold beta_eta1. Lambda_tactics.seq_l. 
unfold Terms.subst. 
unfold abs_K, ap, abs, ref, Terms.subst_rec; fold Terms.subst_rec. 
Lambda_tactics.insert_Ref_out. 
Lambda_tactics.relocate_lt. 
apply Lambda_tactics.succ_red with (abs (Terms.subst  (ap  (Terms.lift_rec (h M) 0 1) (ref 0)) (ref 1))).  
unfold beta_eta1. Lambda_tactics.seq_l. 
unfold Terms.subst. 
unfold abs_K, ap, abs, ref, Terms.subst_rec; fold Terms.subst_rec. 
Lambda_tactics.insert_Ref_out. 
auto. 
eapply2 beta_eta_eq_transitive. 
Qed. 


Lemma trivial_homomorphism1: forall h, homomorphism h -> forall M, beta_eta_eq (h M) (ap (ap (ap (h f_op) abs_I) (h f_op)) (ap (h k_op) (h i_op))). 
Proof. 
assert(forall M, lamSF_red (App (App (App f_op (App (App s_op k_op) M)) f_op) (App k_op i_op)) M). 
split_all. repeat eval_lamSF0. 
split_all. inversion H0. 
assert(beta_eta_eq (h (App (App (App f_op (App (App s_op k_op) M)) f_op) (App k_op i_op))) (h M)) by (split_all; eapply2 H3). 
repeat (rewrite H1 in H0). 
assert(beta_eta_eq (ap (ap (ap (h f_op) (ap (ap (h s_op) (h k_op)) (h M))) (h f_op)) (ap (h k_op) (h i_op)))(ap (ap (ap (h f_op) abs_I) (h f_op)) (ap (h k_op) (h i_op)))). 
repeat(eapply2 preserves_app_beta_eta_eq). 
eapply2 identity_M. 
repeat (rewrite H1 in H6). 
assert(beta_eta_eq (h M) (ap (ap (ap (h f_op) (ap (ap (h s_op) (h k_op)) (h M))) (h f_op))
            (ap (h k_op) (h i_op)))) by eapply2 beta_eta_eq_symmetric. 
eapply2 beta_eta_eq_transitive. 
Qed. 

Lemma trivial_homomorphism: forall h, homomorphism h -> forall M N, beta_eta_eq (h M) (h N). 
Proof. 
split_all. 
eapply beta_eta_eq_transitive. 
eexact (trivial_homomorphism1 h H M). 
eapply beta_eta_eq_symmetric. 
eexact (trivial_homomorphism1 h H N). 
Qed. 

Theorem no_homomorphism: forall h, homomorphism h -> False. 
Proof.
split_all. inversion H. 
assert(beta_eta_eq (h (Ref 0)) (h (Ref 1))) by eapply2 trivial_homomorphism.
repeat (rewrite H1 in H5). 
inversion H5. 
assert(P = ref 0) by eapply2 stable_beta_eta_ref. 
assert(P = ref 1) by eapply2 stable_beta_eta_ref. 
subst. 
inversion H11. 
Qed. 


