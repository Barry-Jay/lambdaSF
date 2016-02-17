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
(* is implemented in Coq by adapting the implementation of            *) 
(* Lambda Calculus  from Project Coq                                  *)
(* 2015                                                               *)
(**********************************************************************)

(**********************************************************************)
(*                     Binding.v                                      *)
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
Require Import Combinators.


Ltac eval_lamSF := eval_lamSF0;  relocate_lt; unfold subst; unfold subst_rec; fold subst_rec; insert_Ref_out; repeat (rewrite lift_rec_null). 

Definition binds_fn := Abs (Abs 
(App (App (App (App equal i_op) (Ref 0)) k_op) 
(App (App (App f_op (Ref 0)) (App k_op i_op)) (Abs (Abs 
(App (App (App (Ref 3) (Ref 1)) k_op) 
(App (Ref 3) (Ref 0))
)))))).

Definition binds := App fixpoint binds_fn. 


Lemma binds_rank : forall M, program M -> rank i_op > rank M -> 
lamSF_red (App binds M) (App k_op i_op).
Proof. 
unfold program; split_all. induction H1; split_all. 
(* 5 *) 
inversion H2; split_all. 
(* 4 *) 
unfold binds.  
fixtac. fold binds. unfold binds_fn. 
eval_lamSF. 
repeat (rewrite (subst_rec_closed equal);  [| split_all]). 
unfold subst_rec; fold subst_rec. insert_Ref_out.
rewrite subst_rec_lift_rec; [|split_all|split_all]. 
match goal with 
| |- multi_step lamSF_red1 (App (App _ ?M)?N) _ => 
apply transitive_red with (App (App (App k_op i_op) M)N) 
end. 
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red. 
eapply2 unequal_programs.
split_all. 
split_all. 
discriminate. 
eval_lamSF. eval_lamSF.  eval_lamSF. auto.
(* 3 *) 
assert(rank M > 0) by eapply2 rank_positive. 
simpl in *. noway. 
(* 2 *) 
assert(status (App M1 M2) <= maxvar (App M1 M2)) by eapply2 status_lt_maxvar. noway.  
(* 1 *) 
unfold binds.  
fixtac. fold binds. unfold binds_fn. 
eval_lamSF. 
repeat (rewrite (subst_rec_closed equal);  [| split_all]). 
unfold subst_rec; fold subst_rec. insert_Ref_out.
repeat(rewrite lift_rec_null). 
match goal with 
| |- multi_step lamSF_red1 (App (App _ ?M)?N) _ => 
apply transitive_red with (App (App (App k_op i_op) M)N) 
end. 
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red. 
eapply2 unequal_programs.
split_all. 
split_all. 
intro. 
rewrite <- H1 in H0. 
simpl in *; noway. 
eval_lamSF. eval_lamSF.  
match goal with 
| |- _ _ (App _ ?N) _ => 
apply succ_red with (App (App N (left_component (App M1 M2))) (right_component (App M1 M2)))
end.
eapply2 f_compound_lamSF_red. 
eval_lamSF. 
repeat (rewrite (subst_rec_closed binds);  [| split_all]). 
unfold left_component, right_component. 
rewrite subst_rec_lift_rec; try omega. 
repeat(rewrite lift_rec_null). 
match goal with 
| |- multi_step lamSF_red1 (App (App _ ?M)?N) _ => 
apply transitive_red with (App (App (App k_op i_op) M)N) 
end. 
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red. 
eapply2 IHnormal1. simpl in *. omega. simpl in *. max_out. 
eval_lamSF. eval_lamSF. 
eapply2 IHnormal2. simpl in *. omega. simpl in *. max_out. 
Qed. 


Lemma binds_abs : forall M, program (Abs M) -> 
lamSF_red (App binds (Abs M)) (App binds (star M)).
Proof. 
unfold program; split_all.  
unfold binds. fixtac. fold binds. unfold binds_fn. eval_lamSF. 
repeat (rewrite (subst_rec_closed equal);  [| split_all]). 
unfold subst_rec; fold subst_rec. insert_Ref_out.
match goal with 
| |- multi_step lamSF_red1 (App (App _ ?M)?N) _ => 
apply transitive_red with (App (App (App k_op i_op) M)N) 
end. 
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red.
rewrite lift_rec_null. 
eapply2 unequal_programs; split_all. 
eval_lamSF. eval_lamSF. 
match goal with 
| |- _ _ (App _ ?N) _ => 
apply succ_red with (App (App N (left_component (Abs M))) (right_component (Abs M)))
end. 
eapply2 f_compound_lamSF_red. 
assert(factorable (Abs M)) . eapply2 programs_are_factorable; split_all. 
inversion H;  split_all. 
eval_lamSF. 
repeat (rewrite (subst_rec_closed binds);  [| split_all]). 
unfold left_component, right_component. 
unfold_op; rewrite subst_rec_lift_rec; try omega. 
rewrite lift_rec_null. 
match goal with 
| |- multi_step lamSF_red1 (App (App _ ?M)?N) _ => 
apply transitive_red with (App (App (App k_op i_op) M)N) 
end. 
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red.
eapply2 binds_rank; split_all; omega. 
eval_lamSF. eval_lamSF. auto. 
Qed. 

Lemma binds_star_0 : forall M, program M -> 
lamSF_red (App binds (star M)) (App k_op i_op). 
Proof. 
cut(forall p M, rank M <= p -> normal M -> maxvar M = 0 -> 
lamSF_red (App binds (star M)) (App k_op i_op)).
split_all.
inversion H0.  
eapply2 H. 
induction p. 
split_all. 
assert(rank M >0) by eapply2 rank_positive; noway. 
(* p > 0 *) 
intros M rnk nor; induction nor; split_all. 
(* 4 *)
unfold_op; eapply2 binds_rank; split_all; omega. 
(* 3 *) 
unfold binds. fixtac. fold binds. unfold binds_fn. eval_lamSF. 
repeat (rewrite (subst_rec_closed equal);  [| split_all]). 
unfold subst_rec; fold subst_rec. insert_Ref_out.
rewrite lift_rec_preserves_star.
match goal with 
| |- multi_step lamSF_red1 (App (App _ ?M)?N) _ => 
apply transitive_red with (App (App (App k_op i_op) M)N) 
end. 
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red. 
rewrite lift_rec_null. 
eapply2 unequal_programs; split_all. 
eapply2 nf_abs. eapply2 normal_star. 
rewrite maxvar_star. omega. 
eval_lamSF. eval_lamSF.
match goal with 
| |- _ _ (App _ ?N) _ => 
apply succ_red with (App (App N (left_component (Abs (star M)))) (right_component (Abs (star M))))
end. 
eapply2 f_compound_lamSF_red. 
eapply2 abs_compound_compound. 
eapply2 star_compound. 
eval_lamSF.  
repeat (rewrite (subst_rec_closed binds);  [| split_all]). 
unfold left_component, right_component. 
unfold_op. rewrite subst_rec_lift_rec; try omega. rewrite lift_rec_null. 
repeat (rewrite (subst_rec_closed equal);  [| split_all]). 
match goal with 
| |- multi_step lamSF_red1 (App (App _ ?M)?N) _ => 
apply transitive_red with (App (App (App k_op i_op) M)N) 
end. 
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red.
eapply2 binds_rank; split_all. 
eval_lamSF; eval_lamSF. 
eapply2 IHp.
assert(rank (star M) < rank (Abs M)) by eapply2 rank_star. 
omega. 
eapply2 normal_star. 
rewrite maxvar_star. auto. 
(* 2 *)
assert(status (App M1 M2) <= maxvar (App M1 M2)) by eapply2 status_lt_maxvar. 
simpl in *; omega. 
(* 1 *) 
unfold binds. fixtac. fold binds. unfold binds_fn. eval_lamSF. 
repeat (rewrite (subst_rec_closed equal);  [| split_all]). 
unfold subst_rec; fold subst_rec. insert_Ref_out.
rewrite subst_rec_lift_rec; [|split_all|split_all]. 
match goal with 
| |- multi_step lamSF_red1 (App (App _ ?M)?N) _ => 
apply transitive_red with (App (App (App k_op i_op) M)N) 
end. 
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red. 
max_out. 
rewrite lift_rec_closed; try (split_all; omega). 
rewrite lift_rec_closed; try (split_all; omega). 
eapply2 unequal_programs; split_all. 
rewrite H1; rewrite H2; split_all. 
eval_lamSF; eval_lamSF. 
eval_lamSF; eval_lamSF; auto. 
repeat (rewrite (subst_rec_closed binds);  [| split_all]). 
unfold subst_rec; fold subst_rec. insert_Ref_out.
rewrite subst_rec_lift_rec; [|split_all|split_all]. 
match goal with 
| |- multi_step lamSF_red1 (App (App _ ?M)?N) _ => 
apply transitive_red with (App (App (App k_op i_op) M)N) 
end. 
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red. 
max_out. 
rewrite lift_rec_closed; try (split_all; omega). 
(* 2 : Abs -> star *)
unfold binds. fixtac. fold binds. unfold binds_fn. eval_lamSF. 
repeat (rewrite (subst_rec_closed equal);  [| split_all]). 
unfold subst_rec; fold subst_rec. insert_Ref_out.
match goal with 
| |- multi_step lamSF_red1 (App (App _ ?M)?N) _ => 
apply transitive_red with (App (App (App k_op i_op) M)N) 
end. 
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red.
rewrite lift_rec_null.  
eapply2 unequal_programs; split_all. 
omega. 
eval_lamSF; eval_lamSF. 
eval_lamSF; eval_lamSF. 
repeat (rewrite (subst_rec_closed binds);  [| split_all]). 
unfold subst_rec; fold subst_rec. insert_Ref_out.
match goal with 
| |- multi_step lamSF_red1 (App (App _ ?M)?N) _ => 
apply transitive_red with (App (App (App k_op i_op) M)N) 
end. 
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red. 
eapply2 binds_rank; split_all. omega. 
eval_lamSF. eval_lamSF.
(* M1 *)  
unfold binds. fold lamSF_red. fixtac. fold binds. unfold binds_fn. eval_lamSF. 
repeat (rewrite (subst_rec_closed equal);  [| split_all]). 
unfold subst_rec; fold subst_rec. insert_Ref_out.
match goal with 
| |- multi_step lamSF_red1 (App (App _ ?M)?N) _ => 
apply transitive_red with (App (App (App k_op i_op) M)N) 
end. 
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red.
rewrite lift_rec_null.  
eapply2 unequal_programs; split_all. 
omega. 
eval_lamSF. eval_lamSF.
match goal with 
| |- _ _ (App _ ?N) _ => 
apply succ_red with (App (App N (left_component (Abs M1))) (right_component (Abs M1)))
end. 
eapply2 f_compound_lamSF_red. 
inversion H; subst; split_all. 
eval_lamSF. 
repeat (rewrite (subst_rec_lift_rec binds); try omega).
unfold left_component, right_component. 
unfold_op; rewrite subst_rec_lift_rec; try omega. 
rewrite lift_rec_null. 
rewrite lift_rec_null. 
match goal with 
| |- multi_step lamSF_red1 (App (App _ ?M)?N) _ => 
apply transitive_red with (App (App (App k_op i_op) M)N) 
end. 
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red. 
eapply2 binds_rank; split_all. 
eval_lamSF. eval_lamSF.
eapply2 IHnor1. 
simpl in *; omega. 
eval_lamSF. eval_lamSF.
(* now M2 *) 
max_out. 
unfold binds. fold lamSF_red. fixtac. fold binds. unfold binds_fn. eval_lamSF. 
repeat (rewrite (subst_rec_closed equal);  [| split_all]). 
unfold subst_rec; fold subst_rec. insert_Ref_out.
match goal with 
| |- multi_step lamSF_red1 (App (App _ ?M)?N) _ => 
apply transitive_red with (App (App (App k_op i_op) M)N) 
end. 
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red.
rewrite lift_rec_null.  
eapply2 unequal_programs; split_all. omega. 
eval_lamSF. eval_lamSF.
match goal with 
| |- _ _ (App _ ?N) _ => 
apply succ_red with (App (App N (left_component (Abs M2))) (right_component (Abs M2)))
end. 
eapply2 f_compound_lamSF_red. 
assert(factorable (Abs M2)) . eapply2 programs_are_factorable; split_all. omega. 
inversion H0; split_all. 
eval_lamSF. 
repeat (rewrite (subst_rec_closed binds);  [| split_all]). 
unfold left_component, right_component. 
unfold_op; rewrite subst_rec_lift_rec; try omega. 
rewrite lift_rec_null. 
match goal with 
| |- multi_step lamSF_red1 (App (App _ ?M)?N) _ => 
apply transitive_red with (App (App (App k_op i_op) M)N) 
end. 
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red. 
eapply2 binds_rank; split_all; omega. 
eval_lamSF. eval_lamSF.
eapply2 IHnor2. 
simpl in *; omega. 
Qed. 



Lemma binds_star_1 : forall M, normal M -> maxvar M = 1 -> 
lamSF_red (App binds (star M)) k_op. 
Proof. 
cut(forall p M, rank M <= p -> normal M -> maxvar M = 1 -> 
lamSF_red (App binds (star M)) k_op).
split_all. 
eapply2 H. 
induction p. 
split_all. 
assert(rank M >0) by eapply2 rank_positive; noway. 
(* p > 0 *) 
intros M rnk nor; induction nor; split_all. 
(* 4 *)
assert(n=0) by omega. subst; split_all. 
unfold binds. fixtac. fold binds. unfold binds_fn. eval_lamSF. 
repeat (rewrite (subst_rec_closed equal);  [| split_all]). 
unfold subst_rec; fold subst_rec. insert_Ref_out.
match goal with 
| |- multi_step lamSF_red1 (App (App _ ?M)?N) _ => 
apply transitive_red with (App (App k_op M)N) 
end. 
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red. 
eapply2 equal_programs; split_all. 
eval_lamSF. auto. 
(* 3 *)
unfold binds. fixtac. fold binds. unfold binds_fn. eval_lamSF. 
repeat (rewrite (subst_rec_closed equal);  [| split_all]). 
unfold subst_rec; fold subst_rec. insert_Ref_out.
rewrite lift_rec_preserves_star.
match goal with 
| |- multi_step lamSF_red1 (App (App _ ?M)?N) _ => 
apply transitive_red with (App (App (App k_op i_op) M)N) 
end. 
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red. 
rewrite lift_rec_null. 
eapply2 unequal_programs; split_all. 
eapply2 nf_abs. eapply2 normal_star. 
rewrite maxvar_star. omega. 
eval_lamSF; eval_lamSF.
match goal with 
| |- _ _ (App _ ?N) _ => 
apply succ_red with (App (App N (left_component (Abs (star M)))) (right_component (Abs (star M))))
end. 
eapply2 f_compound_lamSF_red. 
eapply2 abs_compound_compound. 
eapply2 star_compound. 
eval_lamSF.  
repeat (rewrite (subst_rec_closed binds);  [| split_all]). 
unfold left_component, right_component. 
unfold_op. rewrite subst_rec_lift_rec; try omega. rewrite lift_rec_null. 
unfold subst_rec; fold subst_rec. insert_Ref_out. rewrite lift_rec_null. 
match goal with 
| |- multi_step lamSF_red1 (App (App _ ?M)?N) _ => 
apply transitive_red with (App (App (App k_op i_op) M)N) 
end. 
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red.
eapply2 binds_rank; split_all. 
eval_lamSF; eval_lamSF. 
eapply2 IHp. 
assert(rank (star M) < rank (Abs M)) by eapply2 rank_star. 
omega. 
eapply2 normal_star. 
rewrite maxvar_star. auto. 
(* 2 *)
unfold binds. fixtac. fold binds. unfold binds_fn. eval_lamSF. 
repeat (rewrite (subst_rec_closed equal);  [| split_all]). 
unfold subst_rec; fold subst_rec. insert_Ref_out.
rewrite subst_rec_lift_rec; [|split_all|split_all]. 
match goal with 
| |- multi_step lamSF_red1 (App (App _ ?M)?N) _ => 
apply transitive_red with (App (App (App k_op i_op) M)N) 
end. 
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red. 
rewrite lift_rec_null. rewrite lift_rec_null. 
eapply2 unequal_programs; split_all. 
assert(pred (max(maxvar M1) (maxvar M2)) = 0) by omega. 
rewrite max_pred in H1. 
auto. 
eval_lamSF; eval_lamSF. 
eval_lamSF; eval_lamSF; auto. 
repeat (rewrite (subst_rec_lift_rec binds);  try omega).
rewrite lift_rec_null. 
unfold subst_rec; fold subst_rec. insert_Ref_out.
rewrite subst_rec_lift_rec; [|split_all|split_all]. 
rewrite lift_rec_null. 
unfold binds. fold lamSF_red. fixtac. fold binds. unfold binds_fn. eval_lamSF. 
repeat (rewrite (subst_rec_closed equal);  [| split_all]). 
unfold subst_rec; fold subst_rec. insert_Ref_out.
rewrite subst_rec_lift_rec; [|split_all|split_all]. 
match goal with 
| |- multi_step lamSF_red1 (App (App (App (App _ ?M)?N)?P)?Q) _ => 
apply transitive_red with (App (App (App (App (App k_op i_op) M)N)P)Q)
end. 
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red. 
rewrite lift_rec_null. 
eapply2 unequal_programs; split_all. 
assert(pred (max(maxvar M1) (maxvar M2)) = 0) by omega. 
rewrite max_pred in H1. 
max_out. 
eval_lamSF; eval_lamSF. 
eval_lamSF; eval_lamSF; auto. 
repeat (rewrite (subst_rec_lift_rec binds);  try omega).
rewrite lift_rec_null. 
unfold subst_rec; fold subst_rec. insert_Ref_out.
match goal with 
| |- multi_step lamSF_red1 (App (App (App (App _ ?M)?N)?P)?Q) _ => 
apply transitive_red with (App (App (App (App (App k_op i_op) M)N)P)Q)
end. 
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red. 
eapply2 binds_rank; split_all; omega. 
eval_lamSF.
match goal with 
| |- multi_step lamSF_red1 (App (App _ ?M)?N) _ => 
apply transitive_red with (App (App (App binds (Abs M1))  M)N)
end.
eapply2 preserves_app_lamSF_red. 
assert(pred (max(maxvar M1) (maxvar M2)) = 0) by omega. 
rewrite max_pred in H1. 
max_out. 
apply transitive_red with (App (App (App binds (star M1)) (App (Op Fop) (Op Fop)))
        (App binds (star M2))) .
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red.
eapply2 binds_abs; split_all. 
eapply2 binds_abs; split_all. 
assert(maxvar M1 = 1 \/ maxvar M1 = 0) by omega. 
inversion H1. 
apply transitive_red with (App (App k_op (App (Op Fop) (Op Fop)))
        (App binds (star M2))) .
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red.
eapply2 IHnor1. 
simpl in *; omega. 
eval_lamSF. auto. 
apply transitive_red with (App (App (App k_op i_op) (App (Op Fop) (Op Fop)))
        (App binds (star M2))) .
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red.
eapply2 binds_star_0; split_all. 
eval_lamSF. eval_lamSF. 
rewrite H4 in H0; simpl in H0. 
eapply2 IHnor2; split_all. simpl in *; omega. 
(* 1 *) 
unfold binds. fixtac. fold binds. unfold binds_fn. eval_lamSF. 
repeat (rewrite (subst_rec_closed equal);  [| split_all]). 
unfold subst_rec; fold subst_rec. insert_Ref_out.
rewrite subst_rec_lift_rec; [|split_all|split_all]. 
match goal with 
| |- multi_step lamSF_red1 (App (App _ ?M)?N) _ => 
apply transitive_red with (App (App (App k_op i_op) M)N) 
end. 
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red. 
rewrite lift_rec_null. rewrite lift_rec_null. 
eapply2 unequal_programs; split_all. 
assert(pred (max(maxvar M1) (maxvar M2)) = 0) by omega. 
rewrite max_pred in H1. 
auto. 
eval_lamSF; eval_lamSF. 
eval_lamSF; eval_lamSF; auto. 
repeat (rewrite (subst_rec_lift_rec binds);  try omega).
rewrite lift_rec_null. 
unfold subst_rec; fold subst_rec. insert_Ref_out.
rewrite subst_rec_lift_rec; [|split_all|split_all]. 
rewrite lift_rec_null. 
unfold binds. fold lamSF_red. fixtac. fold binds. unfold binds_fn. eval_lamSF. 
repeat (rewrite (subst_rec_closed equal);  [| split_all]). 
unfold subst_rec; fold subst_rec. insert_Ref_out.
rewrite subst_rec_lift_rec; [|split_all|split_all]. 
match goal with 
| |- multi_step lamSF_red1 (App (App (App (App _ ?M)?N)?P)?Q) _ => 
apply transitive_red with (App (App (App (App (App k_op i_op) M)N)P)Q)
end. 
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red. 
rewrite lift_rec_null. 
eapply2 unequal_programs; split_all. 
assert(pred (max(maxvar M1) (maxvar M2)) = 0) by omega. 
rewrite max_pred in H1. 
max_out. 
eval_lamSF; eval_lamSF. 
eval_lamSF; eval_lamSF; auto. 
repeat (rewrite (subst_rec_lift_rec binds);  try omega).
rewrite lift_rec_null. 
unfold subst_rec; fold subst_rec. insert_Ref_out.
match goal with 
| |- multi_step lamSF_red1 (App (App (App (App _ ?M)?N)?P)?Q) _ => 
apply transitive_red with (App (App (App (App (App k_op i_op) M)N)P)Q)
end. 
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red. 
eapply2 binds_rank; split_all; omega. 
eval_lamSF.
match goal with 
| |- multi_step lamSF_red1 (App (App _ ?M)?N) _ => 
apply transitive_red with (App (App (App binds (Abs M1))  M)N)
end.
eapply2 preserves_app_lamSF_red. 
assert(pred (max(maxvar M1) (maxvar M2)) = 0) by omega. 
rewrite max_pred in H1. 
max_out. 
apply transitive_red with (App (App (App binds (star M1)) (App (Op Fop) (Op Fop)))
        (App binds (star M2))) .
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red.
eapply2 binds_abs; split_all. 
eapply2 binds_abs; split_all. 
assert(maxvar M1 = 1 \/ maxvar M1 = 0) by omega. 
inversion H1. 
apply transitive_red with (App (App k_op (App (Op Fop) (Op Fop)))
        (App binds (star M2))) .
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red.
eapply2 IHnor1. 
simpl in *; omega. 
eval_lamSF. auto. 
apply transitive_red with (App (App (App k_op i_op) (App (Op Fop) (Op Fop)))
        (App binds (star M2))) .
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red.
eapply2 binds_star_0; split_all. 
eval_lamSF. eval_lamSF. 
rewrite H4 in H0; simpl in H0. 
eapply2 IHnor2; split_all. simpl in *; omega. 
Qed. 


Theorem binds_abs_false : 
forall M, program (Abs M) -> closed M -> lamSF_red (App binds (Abs M)) (App k_op i_op). 
Proof. 
split_all.
apply transitive_red with (App binds (star M)). eapply2 binds_abs.  
eapply2 binds_star_0. inversion H. inversion H1.  split_all. 
Qed. 

Theorem binds_abs_true : 
forall M, program (Abs M) -> maxvar M = 1 -> lamSF_red (App binds (Abs M)) k_op.
Proof. 
split_all.
apply transitive_red with (App binds (star M)). eapply2 binds_abs.  
eapply2 binds_star_1. inversion H. inversion H1.  split_all. 
Qed. 

