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
(*                   LamSF_reduction.v                                *)
(*                                                                    *)
(*                     Barry Jay                                      *)
(*                                                                    *)
(**********************************************************************)


Require Import Arith.
Require Import Max. 
Require Import Test.
Require Import General. 
Require Import LamSF_Terms.
Require Import LamSF_Tactics.
Require Import LamSF_Substitution_term.
Require Import Beta_Reduction.
Require Import LamSF_Confluence.
Require Import SF_reduction.

(* lamSF-reduction *) 

Inductive lamSF_red1 : lamSF -> lamSF -> Prop := 
  | appl_lamSF_red :  forall M M' N, lamSF_red1 M M' -> 
                                      lamSF_red1 (App M N) (App M' N)  
  | appr_lamSF_red :  forall M N N', lamSF_red1 N N' -> 
                                      lamSF_red1 (App M N) (App M N')  
  | abs_lamSF_red : forall M M', lamSF_red1 M M' -> lamSF_red1 (Abs M) (Abs M')
  | beta_lamSF_red : forall (M N: lamSF),
                     lamSF_red1 (App (Abs M) N) (subst N M)
  | s_lamSF_red: forall (M N P : lamSF),
             lamSF_red1 
                   (App (App (App (Op Sop) M) N) P) 
                  (App (App M P) (App N P))
  | f_op_lamSF_red : forall M N o,  
               lamSF_red1 (App (App (App (Op Fop) (Op o)) M) N) M 
  | f_compound_lamSF_red : forall (P M N: lamSF), compound P -> 
             lamSF_red1 (App (App (App f_op P) M) N) 
                     (App (App N (left_component P)) (right_component P))
.

Definition lamSF_red := multi_step lamSF_red1. 

Hint Resolve 
appl_lamSF_red appr_lamSF_red abs_lamSF_red 
beta_lamSF_red s_lamSF_red f_op_lamSF_red f_compound_lamSF_red
.


Lemma reflective_lamSF_red: reflective lamSF_red. 
Proof. red; red; reflect. Qed. 
Hint Resolve reflective_lamSF_red.

Definition preserves_apl (red : termred) := 
forall M M' N, red M M' -> red (App M N) (App M' N).

Definition preserves_apr (red : termred) := 
forall M N N', red N N' -> red (App M N) (App M N').

Lemma preserves_apl_multi_step : forall (red: termred), preserves_apl red -> preserves_apl (multi_step red). 
Proof. red. induction 2; split_all. apply succ_red with (App N0 N); auto. Qed. 

Lemma preserves_apr_multi_step : forall (red: termred), preserves_apr red -> preserves_apr (multi_step red). 
Proof. red. induction 2; split_all. apply succ_red with (App M N); auto. Qed. 


Lemma preserves_apl_lamSF_red: preserves_apl lamSF_red. 
Proof. eapply2 preserves_apl_multi_step. red; split_all.  Qed.
Hint Resolve preserves_apl_lamSF_red.

Lemma preserves_apr_lamSF_red: preserves_apr lamSF_red. 
Proof. eapply2 preserves_apr_multi_step. red; split_all.  Qed.
Hint Resolve preserves_apr_lamSF_red.



Lemma preserves_app_lamSF_red: preserves_app lamSF_red. 
Proof. 
red; split_all. 
apply transitive_red with (App M' N); split_all. 
eapply2 preserves_apl_lamSF_red. 
eapply2 preserves_apr_lamSF_red. 
Qed. 
Hint Resolve preserves_app_lamSF_red.

Lemma preserves_abs_lamSF_red: preserves_abs lamSF_red. 
Proof. red; split_all. eapply2 preserves_abs_multi_step. red; split_all. Qed.
Hint Resolve preserves_abs_lamSF_red.

Lemma lift_rec_preserves_lamSF_red1: lift_rec_preserves lamSF_red1. 
Proof. red. intros M N B; induction B; split_all. 
(* 2 *) 
unfold subst. replace n with (0+n) by omega. 
rewrite lift_rec_subst_rec. split_all. 
eapply2 beta_lamSF_red. 
(* 1 *) 
rewrite lift_rec_preserves_components_l. 
rewrite lift_rec_preserves_components_r. 
auto. 
Qed. 

Hint Resolve lift_rec_preserves_lamSF_red1.

Lemma lift_rec_preserves_lamSF_red: lift_rec_preserves lamSF_red. 
Proof. eapply2 lift_rec_preserves_multi_step. Qed. 

Lemma subst_rec_preserves_r_lamSF_red: subst_rec_preserves_r lamSF_red. 
Proof. red. intro M; induction M; split_all. 
unfold insert_Ref. elim(compare k n); split_all. elim a; split_all. 
unfold lift. eapply2 lift_rec_preserves_lamSF_red.
Qed. 


Lemma lamSF_red1_preserves_star_active:
forall M, status M > 0 -> forall N, lamSF_red1 M N -> 
lamSF_red1 (star M) (star N). 
Proof. 
induction M; split_all. 
inversion H0. 
noway. 
inversion H0; split_all. 
eapply2 abs_lamSF_red. 
eapply2 IHM. omega. 
gen2_inv IHM1 H H0; unfold_op; split_all; try noway. 
assert(status P = 0) by eapply2 compound_not_active; noway. 
Qed. 


Lemma lamSF_red1_preserves_star_compound:
forall M, compound M -> forall N, lamSF_red1 M N -> 
lamSF_red1 (star M) (star N). 
Proof. 
induction M; split_all. 
inversion H. 
inversion H. 
(* 2 *)
inversion H0; subst; split_all. 
eapply2 abs_lamSF_red. 
gen2_inv IHM H2 H; subst. 
inversion H1. 
eapply2 lamSF_red1_preserves_star_active. omega. 
(* 1 *) 
gen2_inv IHM1 H0 H; subst. 
inversion H0. inversion H4.  
split_all; unfold_op; split_all; try noway. 
inversion H0. inversion H4.  inversion H8. 
split_all; unfold_op; split_all; try noway. 
split_all; unfold_op; split_all; try noway. 
Qed. 


Lemma preserves_status_lamSF_red1 : 
forall M, status M > 0 -> forall N, lamSF_red1 M N -> status M = status N.
Proof. 
cut(forall p M, p>= rank M -> status M >0 -> forall N, lamSF_red1 M N -> status M = status N). 
split_all; eapply2 H. 
induction p; split_all. 
assert(rank M >0) by eapply2 rank_positive. noway. 
(* p >0 *) 
induction M; intros. 
inversion H1; split_all.
simpl in *; noway.
inversion H1; split_all.
(* 2 *) 
cut(status M = status M'); split_all; eapply2 IHp; simpl in *; omega. 
(* 1 *) 
generalize IHM1 H H0 H1; clear IHM1 H H0 H1; case M1; intros.  
inversion H1. inversion H5; split_all. 
simpl in *.  auto. 
simpl in H0. noway. 
simpl in H0. noway. 
(* 1 *) 
generalize IHM1 H H0 H1; clear IHM1 H H0 H1; case l; intros.  
inversion H1. inversion H5.  inversion H9; split_all. 
split_all. 
split_all. 
simpl in *; noway. 
simpl in *; noway. 
(* 1 *) 
generalize IHM1 H H0 H1; clear IHM1 H H0 H1; case l1; intros.  
inversion H1. inversion H5.  inversion H9.  inversion H13; split_all. 
split_all. 
split_all. 
split_all. 
generalize IHM1 H H0 H1; clear IHM1 H H0 H1; case o; split_all; try noway.
gen_inv H0 H1. subst. 
inversion H4. 
inversion H6.  
inversion H10. 
eapply2 IHp.
omega. 
auto. 
noway. 
assert(status l2 = 0) by eapply2 compound_not_active. noway. 
simpl in H0; noway. 
(* 1 *) 
generalize H0; clear H0; inversion H1; intro. 
assert(exists m3 m4 m2 m0, M' = App (App (App m3 m4) m2) m0). 
generalize H5; clear H5; inversion H4; intro. 
generalize H9; clear H9; inversion H8; intro. 
generalize H13; clear H13; inversion H12; intro. 
exist M'2; exist l4; exist l2; exist l0. 
exist l3; exist N'; exist l2; exist l0. 
simpl in H16; noway. 
simpl in H16; noway. 
simpl in H16; noway. 
simpl in H17.  assert(status P = 0) by eapply2 compound_not_active. noway. 
exist l3; exist l4; exist N'; exist l0.
simpl in H13; noway. 
simpl in H13; noway. 
simpl in H14.   assert(status P = 0) by eapply2 compound_not_active. noway. 
exist l3; exist l4; exist l2; exist N'. 
simpl in H10; noway. 
simpl in H10; noway. 
simpl in H11.   assert(status l4 = 0) by eapply2 compound_not_active. noway. 
inversion H6; inversion H7; inversion H8; inversion H9. subst.
assert(status (App (App (App (App l3 l4) l2) l0) M2) = status  (App (App (App l3 l4) l2) l0)) by split_all. 
rewrite H0 in H5. 
rewrite H0. 
assert(status (App (App (App (App x x0) x1) x2) M2) = status (App (App (App x x0) x1) x2)) by split_all. 
rewrite H2.  
eapply2 IHp. 
simpl in *; omega. 
auto. 
Qed. 



Lemma preserves_compound_lamSF_red1: forall M N : lamSF,
   lamSF_red1 M N ->
   compound M ->
   compound N /\
   lamSF_red (left_component M) (left_component N) /\
   lamSF_red (right_component M) (right_component N).
Proof. 
intros M N R; induction R; intro c; inversion c; split_all; subst; 
inv lamSF_red1. 
red; one_step; unfold_op; eapply2 abs_lamSF_red. 
red; one_step; unfold_op; eapply2 abs_lamSF_red. 
red; one_step; unfold_op; eapply2 abs_lamSF_red. 
eapply2 abs_compound_compound. eapply2 IHR.  
red; one_step. 
unfold_op; repeat (eapply2 appl_lamSF_red); repeat(eapply2 appr_lamSF_red). 
eapply2 lamSF_red1_preserves_star_compound. 
eapply2 abs_active_compound. 
assert(status M = status M'). 
eapply2 preserves_status_lamSF_red1. 
omega. omega. 
red; one_step. 
eapply2 lamSF_red1_preserves_star_active. 
omega. 
Qed. 




Ltac app_bop := unfold_op; 
match goal with 
| |- bop _ _ => red; app_bop
| |- multi_step bop1 (Ref _) (Ref _) => red; one_step; app_bop
| |- multi_step bop1 f_op f_op => red; one_step; app_bop
| |- multi_step bop1 (Abs _) (Abs _) => eapply2 preserves_abs_bop ; app_bop
| |- multi_step bop1 (App _ _) (App _ _) => eapply2 preserves_app_bop ; app_bop
| |- multi_step bop1 (left_component _) (left_component _) => eapply2 preserves_compound_bop; app_bop 
| |- multi_step bop1 (right_component _) (right_component _) => eapply2 preserves_compound_bop; app_bop
| |- multi_step bop1 (lift_rec _ _ _) (lift_rec _ _ _) => eapply2 lift_rec_preserves_bop; app_bop
| |- bop1 (App _ _) (App _ _) => eapply2 preserves_app_bop1 ; app_bop
| |- bop1 (left_component _) (left_component _) => eapply2 preserves_compound_bop1; app_bop 
| |- bop1 (right_component _) (right_component _) => eapply2 preserves_compound_bop1; app_bop
| |- bop1 (lift_rec _ _ _) (lift_rec _ _ _) => eapply2 lift_rec_preserves_bop1; app_bop
| H : bop1 _ _ |- compound _ => eapply2 preserves_compound_bop1
| |- bop1 (left_component _) _ => eapply2 preserves_compound_bop1
| |- bop1 (right_component _) _ => eapply2 preserves_compound_bop1
| _ => try red; split_all
end.



Ltac app_lamSF := unfold_op; 
match goal with 
| |- lamSF_red _ _ => red; app_lamSF
| |- multi_step lamSF_red1 (Ref _) (Ref _) => red; one_step
| |- multi_step lamSF_red1 f_op f_op => red; one_step; app_lamSF
| |- multi_step lamSF_red1 (App _ _) (App _ _) => eapply2 preserves_app_lamSF_red ; app_lamSF
| |- multi_step lamSF_red1 (Abs _) (Abs _) => eapply2 preserves_abs_lamSF_red ;app_lamSF
| |- lamSF_red1 (Abs _) (Abs _) => eapply2 abs_lamSF_red ; app_lamSF
| |- lamSF_red1 (lift_rec _ _ _) (lift_rec _ _ _) => eapply2 lift_rec_preserves_lamSF_red1; app_lamSF
| _ => try red; split_all
end.


Ltac seq_l := 
match goal with 
| |- sequential _ _ ?M ?N => apply seq_red with N; auto
end.
Ltac seq_r := 
match goal with 
| |- sequential _ _ ?M ?N => apply seq_red with M; auto
end.

Definition implies_red (red1 red2: termred) := forall M N, red1 M N -> red2 M N. 

Lemma implies_red_multi_step: forall red1 red2, implies_red red1  (multi_step red2) -> 
                                                implies_red (multi_step red1) (multi_step red2).
Proof. red. 
intros red1 red2 IR M N R; induction R; split_all. 
apply transitive_red with N; auto. 
Qed. 
Lemma implies_red_seq: 
 forall red1 red2 red3, 
  implies_red red1  (multi_step red3)  ->  
  implies_red red2 (multi_step red3) -> 
  implies_red (sequential red1 red2) (multi_step red3) .
Proof. 
red; split_all. inversion H1. apply transitive_red with N0; auto. 
Qed. 


Lemma lamSF_red1_to_bop1 : implies_red lamSF_red1 bop1. 
Proof. 
Ltac aux M := 
apply succ_red with M; split_all; [red; seq_r; red; one_step | app_bop]. 

red. intros M N B; induction B; split_all; 
try (red; seq_r; red; one_step; fail);
try (red; seq_l; red; seq_l; red; one_step; fail);
try (red; seq_l; red; seq_r; red; one_step; fail).
inversion IHB; subst. 
red. apply seq_red with (Abs N); split_all.
Qed. 



Lemma lamSF_red_to_bop: implies_red lamSF_red bop. 
Proof. 
eapply2 implies_red_multi_step. 
red; split_all; one_step; eapply2 lamSF_red1_to_bop1. 
Qed. 



Lemma to_lamSF_red_multi_step: forall red, implies_red red lamSF_red -> implies_red (multi_step red) lamSF_red. 
Proof. 
red.  intros red B M N R; induction R; split_all.
red; split_all. 
assert(lamSF_red M N) by eapply2 B. 
apply transitive_red with N; auto. 
eapply2 IHR. 
Qed. 

Lemma to_lamSF_red_seq: forall red1 red2, implies_red red1 lamSF_red -> implies_red red2 lamSF_red -> 
implies_red  (sequential red1 red2) lamSF_red. 
Proof. 
red; split_all. inversion H1; subst. apply transitive_red with N0; auto. eapply2 H. eapply2 H0.  Qed. 

Ltac aux M ::= apply succ_red with M; [split_all | app_lamSF];
match goal with 
| |- lamSF_red1 _ (App (App _ ?P)?Q) => 
replace P with (left_component (App P Q)) by auto;  
replace Q with (right_component (App P Q)) by auto; auto
end. 

Definition preserves_components_l (red: termred) := 
forall M, compound M -> forall N, red M N -> compound N /\ 
multi_step red (left_component M) (left_component N).

Lemma preserves_components_l_multi_step : 
forall red, preserves_components_l red -> 
forall M, compound M -> forall N, multi_step red M N -> compound N /\ 
multi_step red (left_component M) (left_component N).
Proof. 
intros red p M c N R; induction R; split_all. 
eapply2 IHR. eapply2 p. 
apply transitive_red with (left_component N); split_all. 
eapply2 p. eapply2 IHR. eapply2 p. 
Qed. 




Definition preserves_components_r (red: termred) := 
forall M, compound M -> forall N, red M N -> compound N /\ 
multi_step red (right_component M) (right_component N).


Lemma preserves_components_r_multi_step : 
forall red, preserves_components_r red -> 
forall M, compound M -> forall N, multi_step red M N -> compound N /\ 
multi_step red (right_component M) (right_component N).
Proof. 
intros red p M c N R; induction R; split_all. 
eapply2 IHR. eapply2 p. 
apply transitive_red with (right_component N); split_all. 
eapply2 p. eapply2 IHR. eapply2 p. 
Qed. 


Lemma preserves_components_l_lamSF_red1 :  preserves_components_l lamSF_red1. 
Proof. 
red; split_all.  gen_inv H H0; inv1 compound; subst; split_all. 
(* 6 *) 
inversion H. 
(* 5 *) 
inversion H. inversion H4. split_all. 
(* 4 *) 
inversion H. 
(* 3 *) 
eapply2 abs_compound_compound. 
eapply2 preserves_compound_lamSF_red1. 
(* 2 *) 
eapply2 abs_active_compound. 
assert(status M0 = status M'). eapply2 preserves_status_lamSF_red1. 
omega. 
omega. 
(* 1 *) 
gen_inv H0 H. 
(* 5 *) 
inversion H1. inversion H5. split_all.  
(* 4 *) 
inversion H1. inversion H5. inversion H9; split_all. 
one_step. split_all. 
(* 3 *) 
inversion H1. inversion H3. 
(* 2 *) 
inversion H2. split_all. 
(* 1 *) 
inversion H2; split_all. 
Qed. 


Lemma preserves_components_r_lamSF_red1 :  preserves_components_r lamSF_red1. 
Proof. 
red; split_all.  gen_inv H H0; inv1 compound; subst; split_all. 
(* 6 *) 
inversion H. 
(* 5 *) 
inversion H. inversion H4. split_all. 
(* 4 *) 
inversion H. 
(* 3 *)
eapply2 abs_compound_compound. 
eapply2 preserves_compound_lamSF_red1. 
eapply2 abs_active_compound. 
assert(status M0 = status M'). eapply2 preserves_status_lamSF_red1. 
omega. 
omega. 
(* 1 *) 
gen_inv H H0; inv1 compound; subst; split_all; try one_step. 
(* 3 *)
inversion H.  
unfold_op; repeat(eapply2 appl_lamSF_red); repeat (eapply2 appr_lamSF_red). 
eapply2 lamSF_red1_preserves_star_compound. 
eapply2 lamSF_red1_preserves_star_active. omega. 
Qed. 


Lemma opred1_to_lamSF_red: implies_red opred1 lamSF_red. 
Proof. 
red.  intros M N OR; induction OR; split_all.
(* 3 *) 
apply succ_red with (App (App M P) (App N P)). eapply2 s_lamSF_red. 
eapply2 preserves_app_lamSF_red. 
apply succ_red with M. 
eapply2 f_op_lamSF_red. auto. 
red; apply succ_red with  (App (App N (left_component P)) (right_component P))
; split_all. 
app_lamSF. 
fold lamSF_red. 
eapply2 preserves_components_l_multi_step. 
eapply2 preserves_components_l_lamSF_red1. 
eapply2 preserves_components_r_multi_step. 
eapply2 preserves_components_r_lamSF_red1. 
Qed. 

Hint Resolve opred1_to_lamSF_red.

Lemma par_red1_to_lamSF_red: implies_red par_red1 lamSF_red. 
Proof. 
red.  intros M N PR; induction PR; split_all. 
apply transitive_red with (App (Abs M') N'); auto. app_lamSF. one_step.
Qed.
Hint Resolve par_red1_to_lamSF_red.

Lemma bop1_to_lamSF_red: implies_red bop1 lamSF_red. 
Proof. 
eapply2 implies_red_seq. 
eapply2 implies_red_multi_step. 
Qed. 

Lemma bop_to_lamSF_red: implies_red bop lamSF_red. 
Proof. 
eapply2 implies_red_multi_step.
eapply2 bop1_to_lamSF_red. 
Qed. 


Lemma diamond_lamSF_red: diamond lamSF_red lamSF_red. 
Proof. 
red; split_all. 
assert(bop M N) by eapply2 lamSF_red_to_bop.  
assert(bop M P) by eapply2 lamSF_red_to_bop.  
elim(diamond_bop M N H1 P); split_all. 
exist x; eapply2 bop_to_lamSF_red. 
Qed. 
Hint Resolve diamond_lamSF_red. 

Theorem confluence_lamSF_red: confluence lamSF lamSF_red.
Proof. red; eapply2 diamond_lamSF_red. Qed. 

(* restore if needed 

Definition lamSF_eq M N := exists P, lamSF_red M P /\ lamSF_red N P.

Ltac is_lamSF := match goal with 
| |- lamSF_eq _ ?M => exist M
end. 

Ltac is_lamSF_l :=
match goal with 
| |- lamSF_eq ?M ?N => exist M; split_all
end. 


Lemma reflexive_lamSF_eq: forall M, lamSF_eq M M.
Proof. split_all; exist M. Qed. 
Hint Resolve reflexive_lamSF_eq.

Lemma transitive_lamSF_eq: transitive lamSF_eq. 
Proof. 
unfold transitive; split_all. 
inversion H; inversion H0; split_all.  
elim(diamond_lamSF_red N x0 H3 x); split_all. 
exist x1. 
apply transitive_red with x; split_all. 
apply transitive_red with x0; split_all. 
Qed. 

Lemma symmetric_lamSF_eq: forall M N, lamSF_eq M N -> lamSF_eq N M. 
Proof. 
split_all. 
inversion H; split_all.  
exist x. 
Qed. 

Lemma app_preserves_lamSF_eq : 
forall M1 N1, lamSF_eq M1 N1 -> forall M2 N2, lamSF_eq M2 N2 -> lamSF_eq (App M1 M2) (App N1 N2). 
Proof. unfold lamSF_eq; split_all. exist (App x0 x). Qed. 

Lemma abs_preserves_lamSF_eq : 
forall M1 N1, lamSF_eq M1 N1 -> lamSF_eq (Abs M1) (Abs N1). 
Proof. unfold lamSF_eq; split_all. exist (Abs x). Qed. 

Lemma  lift_rec_preserves_lamSF_eq: forall M N, lamF_eq M N -> 
forall n k, lamF_eq (lift_rec M n k) (lift_rec N n k). 
Proof. 
red; intros. inversion H; split_all. exist (lift_rec x n k); eapply2 lift_rec_preserves_lamF_red. 
Qed. 


Definition subst_rec_preserves_l_eq (red: termred) := 
forall (M M' N : lamF), red M M' -> forall ( k : nat), lamF_eq  (subst_rec M N k) (subst_rec M' N k).

Lemma subst_rec_preserves_l_eq_multi_step : 
forall (red: termred), subst_rec_preserves_l_eq red -> subst_rec_preserves_l_eq (multi_step red). 
Proof. red. 
 induction 2; split_all.
apply transitive_lamF_eq with (subst_rec N0 N k); split_all. 
Qed.

Lemma subst_rec_preserves_l_eq_lamF_red1: subst_rec_preserves_l_eq lamF_red1.
Proof. 
red.
assert(forall M M' : lamF,
   lamF_red1 M M' ->
   forall N (k : nat), lamF_eq (subst_rec M N k) (subst_rec M' N k)). 
2: split_all; eapply2 H. 

  intros M M' R; induction R; split_all; try (is_lamF; fail). 
(* 5 subgoals *) 
eapply2 app_preserves_lamF_eq. 
eapply2 app_preserves_lamF_eq. 
eapply2 abs_preserves_lamF_eq.
(* 2 *) 
 unfold subst. 
replace k with (0+k) by omega. 
rewrite subst_rec_subst_rec. 
is_lamF. red; one_step. 
eapply2 beta_lamF_red. 
(* 1 *) 
is_lamF. red; one_step. 
rewrite subst_rec_preserves_components_l; split_all. 
rewrite subst_rec_preserves_components_compound_r. 
eapply2 f_compound_lamF_red. 
auto. 
Qed. 

Lemma subst_rec_preserves_l_eq_lamF_red: subst_rec_preserves_l_eq lamF_red. 
Proof. 
eapply2 subst_rec_preserves_l_eq_multi_step. 
eapply2 subst_rec_preserves_l_eq_lamF_red1. 
Qed. 

Lemma subst_rec_preserves_eq_lamF_red:
forall (M M' : lamF), lamF_red M M' -> forall N N', lamF_red N N' -> forall ( k : nat), lamF_eq  (subst_rec M N k) (subst_rec M' N' k).
Proof. 
split_all. 
apply transitive_lamF_eq with (subst_rec M N' k). 
is_lamF. eapply2 subst_rec_preserves_r_lamF_red. 
eapply2 subst_rec_preserves_l_eq_lamF_red. 
Qed. 

Lemma subst_rec_preserves_lamF_eq:
forall (M M' : lamF), lamF_eq M M' -> forall N N', lamF_eq N N' -> forall ( k : nat), lamF_eq  (subst_rec M N k) (subst_rec M' N' k).
Proof. 
split_all. inversion H; inversion H0; split_all. 
apply transitive_lamF_eq with (subst_rec x x0 k). 
eapply2 subst_rec_preserves_eq_lamF_red. 
eapply2 symmetric_lamF_eq.
eapply2 subst_rec_preserves_eq_lamF_red. 
Qed. 

Lemma preserves_compound_lamF_eq: 
forall M N, compound M -> compound N -> lamF_eq M N -> 
lamF_eq (left_component M) (left_component N) /\ 
lamF_eq (right_component M) (right_component N).
Proof. 
intros. 
inversion H1.  split_all. 
exist(left_component x);
eapply2 preserves_components_l_multi_step; 
eapply2 preserves_components_l_lamF_red1. 
exist(right_component x);
eapply2 preserves_components_r_multi_step;
eapply2 preserves_components_r_lamF_red1. 
Qed. 
 
*) 