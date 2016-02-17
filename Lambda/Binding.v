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
Require Import Terms.
Require Import Substitution_term.
Require Import Lambda_tactics.
Require Import Reduction.
Require Import Confluence.
Require Import SF_reduction.
Require Import LamSF_reduction.
Require Import Normal.
Require Import Closed.
Require Import Eval.
Require Import Equal.
Require Import Combinators.


Ltac eval_lamSF := eval_lamSF0;  relocate_lt; unfold subst; unfold subst_rec; fold subst_rec; insert_Ref_out; repeat (rewrite lift_rec_null). 

Definition binds_fn := Abs (Abs 
(App (App (App (App equal_comb i_op) (Ref 0)) k_op) 
(App (App (App f_op (Ref 0)) (App k_op i_op)) (Abs (Abs 
(App (App (App (App equal_comb k_op) (Ref 1)) (App k_op i_op))
(App (App (App (Ref 3) (Ref 1)) k_op) 
(App (Ref 3) (Ref 0))
))))))).

Definition binds := App fixpoint binds_fn. 

Lemma binds_K : forall M, lamSF_red (App binds (App k_op M)) (App k_op i_op).
Proof. 
split_all. unfold binds.  fixtac. fold binds. unfold binds_fn. 
eval_lamSF. 
repeat (rewrite (subst_rec_closed equal_comb);  [| split_all]). 
unfold subst_rec; fold subst_rec. insert_Ref_out.
rewrite lift_rec_null.
match goal with 
| |- multi_step lamSF_red1 (App (App _ ?M)?N) _ => 
apply transitive_red with (App (App (App k_op i_op) M)N) 
end. 
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red. 
apply transitive_red with (App (App (App (App equal_comb (left_component i_op)) (left_component (App k_op M)))(App (App equal_comb (right_component i_op)) (right_component (App k_op M)))) (App k_op i_op)). 
eapply equal_compounds. 
unfold_op; split_all. 
unfold_op; split_all. 
simpl. 
match goal with 
| |- multi_step lamSF_red1 (App (App _ ?M)?N) _ => 
apply transitive_red with (App (App (App k_op i_op) M)N) 
end. 
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red. 
eapply2 unequal_closed_normal_forms.
unfold_op; split_all. 
unfold_op; split_all. 
discriminate. 
eval_lamSF. eval_lamSF.  auto. 
eval_lamSF. eval_lamSF.  eval_lamSF. eval_lamSF. 
repeat (rewrite (subst_rec_closed equal_comb);  [| split_all]). 
unfold subst_rec; fold subst_rec. insert_Ref_out.
match goal with 
| |- multi_step lamSF_red1 (App (App _ ?M)?N) _ => 
apply transitive_red with (App (App k_op M)N) 
end. 
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red. 
eapply2 equal_closed_normal_forms.
eval_lamSF. auto.
Qed. 


Lemma binds_rank : forall M, normal M -> maxvar M = 0 -> rank i_op > rank M -> 
lamSF_red (App binds M) (App k_op i_op).
Proof. 
intros M nor; induction nor; split_all. 
(* 4 *) 
unfold binds.  
fixtac. fold binds. unfold binds_fn. 
eval_lamSF. 
repeat (rewrite (subst_rec_closed equal_comb);  [| split_all]). 
unfold subst_rec; fold subst_rec. insert_Ref_out.
rewrite subst_rec_lift_rec; [|split_all|split_all]. 
match goal with 
| |- multi_step lamSF_red1 (App (App _ ?M)?N) _ => 
apply transitive_red with (App (App (App k_op i_op) M)N) 
end. 
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red. 
eapply2 unequal_closed_normal_forms.
discriminate. 
eval_lamSF. eval_lamSF.  eval_lamSF. auto.
(* 3 *) 
assert(rank M > 0) by eapply2 rank_positive. 
noway. 
(* 2 *) 
assert(status (App M1 M2) <= maxvar (App M1 M2)) by eapply2 status_lt_maxvar. 
unfold maxvar in H2; fold maxvar in H2. noway. 
(* 1 *) 
unfold binds.  
fixtac. fold binds. unfold binds_fn. 
eval_lamSF. 
repeat (rewrite (subst_rec_closed equal_comb);  [| split_all]). 
unfold subst_rec; fold subst_rec. insert_Ref_out.
repeat(rewrite lift_rec_null). 
match goal with 
| |- multi_step lamSF_red1 (App (App _ ?M)?N) _ => 
apply transitive_red with (App (App (App k_op i_op) M)N) 
end. 
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red. 
eapply2 unequal_closed_normal_forms.
intro. inversion H2; subst. 
simpl in *; noway. 
eval_lamSF. eval_lamSF.  
match goal with 
| |- _ _ (App _ ?N) _ => 
apply succ_red with (App (App N (left_component (App M1 M2))) (right_component (App M1 M2)))
end.
eapply2 f_compound_lamSF_red. 
eval_lamSF. 
repeat (rewrite (subst_rec_closed equal_comb);  [| split_all]). 
unfold left_component, right_component. 
rewrite subst_rec_lift_rec; try omega. 
repeat(rewrite lift_rec_null). 
assert(k_op = M1 \/ k_op <> M1) by eapply2 decidable_term_equality. 
inversion H2. 
match goal with 
| |- multi_step lamSF_red1 (App (App _ ?M)?N) _ => 
apply transitive_red with (App (App k_op M)N) 
end. 
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red. 
rewrite <- H3. 
eapply2 equal_closed_normal_forms.
unfold_op; split_all. 
eval_lamSF. auto. 
match goal with 
| |- multi_step lamSF_red1 (App (App _ ?M)?N) _ => 
apply transitive_red with (App (App (App k_op i_op) M)N) 
end. 
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red. 
eapply2 unequal_closed_normal_forms.
max_out. 
eval_lamSF. eval_lamSF.  
repeat(rewrite (subst_rec_lift_rec binds); try (split_all; omega)). 
rewrite lift_rec_null. 
apply transitive_red with (App (App (App k_op i_op) k_op) (App k_op i_op)).
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red. 
eapply2 IHnor1. max_out. simpl. omega. 
eapply2 IHnor2. max_out. simpl. omega. 
repeat (eval_lamSF). auto. 
Qed. 

(* delete 

Lemma binds_abs_tag : lamSF_red (App binds abs_tag) (App k_op i_op). 
Proof. 
unfold binds. fixtac. fold binds. unfold binds_fn. eval_lamSF. 
repeat (rewrite (subst_rec_closed equal_comb);  [| split_all]). 
unfold subst_rec; fold subst_rec. insert_Ref_out.
match goal with 
| |- multi_step lamSF_red1 (App (App _ ?M)?N) _ => 
apply transitive_red with (App (App (App k_op i_op) M)N) 
end. 
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red. 
eapply2 unequal_closed_normal_forms. 
discriminate. 
eval_lamSF. eval_lamSF. eval_lamSF. eval_lamSF.
repeat (rewrite (subst_rec_closed equal_comb);  [| split_all]). 
unfold subst_rec; fold subst_rec. insert_Ref_out.
match goal with 
| |- multi_step lamSF_red1 (App (App _ ?M)?N) _ => 
apply transitive_red with (App (App (App k_op i_op) M)N) 
end. 
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red. 
eapply2 unequal_closed_normal_forms. 
discriminate. 
eval_lamSF. eval_lamSF. 
repeat (rewrite (subst_rec_closed binds);  [| split_all]). 
match goal with 
| |- multi_step lamSF_red1 (App (App _ ?M)?N) _ => 
apply transitive_red with (App (App (App k_op i_op) M)N) 
end. 
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red. 
eapply2 binds_rank; simpl; omega. 
eval_lamSF. eval_lamSF. 
eapply2 binds_rank; simpl; omega. 
Qed. 

*) 

Lemma binds_star_0 : forall M, normal M -> maxvar M = 0 -> 
lamSF_red (App binds (star M)) (App k_op i_op). 
Proof. 
cut(forall p M, rank M <= p -> normal M -> maxvar M = 0 -> 
lamSF_red (App binds (star M)) (App k_op i_op)).
split_all. 
eapply2 H. 
induction p. 
split_all. 
assert(rank M >0) by eapply2 rank_positive; noway. 
(* p > 0 *) 
intros M rnk nor; induction nor; split_all. 
(* 4 *)
unfold_op; eapply2 binds_rank; simpl; omega. 
(* 3 *) 
unfold binds. fixtac. fold binds. unfold binds_fn. eval_lamSF. 
repeat (rewrite (subst_rec_closed equal_comb);  [| split_all]). 
unfold subst_rec; fold subst_rec. insert_Ref_out.
rewrite lift_rec_preserves_star.
match goal with 
| |- multi_step lamSF_red1 (App (App _ ?M)?N) _ => 
apply transitive_red with (App (App (App k_op i_op) M)N) 
end. 
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red. 
rewrite lift_rec_null. 
eapply2 unequal_closed_normal_forms. 
eapply2 nf_abs. eapply2 normal_star. 
simpl. 
rewrite maxvar_star. omega. 
discriminate. 
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
repeat (rewrite (subst_rec_closed equal_comb);  [| split_all]). 
match goal with 
| |- multi_step lamSF_red1 (App (App _ ?M)?N) _ => 
apply transitive_red with (App (App (App k_op i_op) M)N) 
end. 
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red.
eapply2 unequal_closed_normal_forms. 
discriminate.
eval_lamSF; eval_lamSF. 
match goal with 
| |- multi_step lamSF_red1 (App (App _ ?M)?N) _ => 
apply transitive_red with (App (App (App k_op i_op) M)N) 
end. 
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red.
eapply2 binds_rank. 
simpl. omega. 
eval_lamSF. eval_lamSF. 
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
repeat (rewrite (subst_rec_closed equal_comb);  [| split_all]). 
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
eapply2 unequal_closed_normal_forms. 
simpl. 
rewrite H1; rewrite H2; split_all. 
discriminate. 
eval_lamSF; eval_lamSF. 
eval_lamSF; eval_lamSF; auto. 
repeat (rewrite (subst_rec_closed equal_comb);  [| split_all]). 
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
eapply2 unequal_closed_normal_forms. 
simpl. 
rewrite H1; split_all. 
discriminate. 
eval_lamSF; eval_lamSF. 
rewrite subst_rec_lift_rec; [|split_all|split_all]. 
rewrite subst_rec_lift_rec; [|split_all|split_all]. 
rewrite lift_rec_null.
(* 2 : Abs -> star *)
apply transitive_red with (App (App (App k_op i_op) k_op) (App k_op i_op)).
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red.
unfold binds. fold lamSF_red. fixtac. fold binds. unfold binds_fn. eval_lamSF. 
repeat (rewrite (subst_rec_closed equal_comb);  [| split_all]). 
unfold subst_rec; fold subst_rec. insert_Ref_out.
match goal with 
| |- multi_step lamSF_red1 (App (App _ ?M)?N) _ => 
apply transitive_red with (App (App (App k_op i_op) M)N) 
end. 
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red.
eapply2 unequal_closed_normal_forms. 
eapply2 nf_compound. 
eapply2 nf_abs. 
eapply2 lift_rec_preserves_normal.
max_out; simpl. 
rewrite lift_rec_closed; try (split_all; omega). 
discriminate. 
eval_lamSF; eval_lamSF. 
eval_lamSF; eval_lamSF. 
repeat (rewrite (subst_rec_closed equal_comb);  [| split_all]). 
unfold subst_rec; fold subst_rec. insert_Ref_out.
match goal with 
| |- multi_step lamSF_red1 (App (App _ ?M)?N) _ => 
apply transitive_red with (App (App (App k_op i_op) M)N) 
end. 
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red. 
eapply2 unequal_closed_normal_forms. 
discriminate. 
eval_lamSF. eval_lamSF.
rewrite subst_rec_lift_rec; try omega. 
rewrite subst_rec_lift_rec; try omega. 
rewrite subst_rec_lift_rec; try omega. 
rewrite lift_rec_null.
match goal with 
| |- multi_step lamSF_red1 (App (App _ ?M)?N) _ => 
apply transitive_red with (App (App (App k_op i_op) M)N) 
end. 
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red. 
eapply2 binds_rank. 
unfold_op; split_all; omega.  
eval_lamSF. eval_lamSF. 
simpl.
(* M1 *)  
unfold binds. fold lamSF_red. fixtac. fold binds. unfold binds_fn. eval_lamSF. 
repeat (rewrite (subst_rec_closed equal_comb);  [| split_all]). 
unfold subst_rec; fold subst_rec. insert_Ref_out.
match goal with 
| |- multi_step lamSF_red1 (App (App _ ?M)?N) _ => 
apply transitive_red with (App (App (App k_op i_op) M)N) 
end. 
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red. 
eapply2 unequal_closed_normal_forms. 
eapply2 nf_abs. 
eapply2 lift_rec_preserves_normal. 
simpl. 
max_out. rewrite lift_rec_closed; try (split_all; omega). 
discriminate. 
eval_lamSF. eval_lamSF.
match goal with 
| |- _ _ (App _ ?N) _ => 
apply succ_red with (App (App N (left_component (Abs M1))) (right_component (Abs M1)))
end. 
eapply2 f_compound_lamSF_red. 
inversion H; subst; split_all. 
eval_lamSF. 
repeat (rewrite (subst_rec_closed equal_comb);  [| split_all]). 
unfold left_component, right_component. 
unfold_op; rewrite subst_rec_lift_rec; try omega. 
rewrite lift_rec_null. 
match goal with 
| |- multi_step lamSF_red1 (App (App _ ?M)?N) _ => 
apply transitive_red with (App (App (App k_op i_op) M)N) 
end. 
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red. 
eapply2 unequal_closed_normal_forms. 
discriminate. 
eval_lamSF. eval_lamSF.
rewrite subst_rec_lift_rec; try omega. 
rewrite subst_rec_lift_rec; try omega. 
rewrite subst_rec_lift_rec; try omega. 
rewrite lift_rec_null.
match goal with 
| |- multi_step lamSF_red1 (App (App _ ?M)?N) _ => 
apply transitive_red with (App (App (App k_op i_op) M)N) 
end. 
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red. 
eapply2 binds_rank; simpl; omega. 
eval_lamSF. eval_lamSF. 
eapply2 IHnor1. 
simpl in *; omega. 
max_out. 
(* now M2 *) 
unfold binds. fold lamSF_red. fixtac. fold binds. unfold binds_fn. eval_lamSF. 
repeat (rewrite (subst_rec_closed equal_comb);  [| split_all]). 
unfold subst_rec; fold subst_rec. insert_Ref_out.
match goal with 
| |- multi_step lamSF_red1 (App (App _ ?M)?N) _ => 
apply transitive_red with (App (App (App k_op i_op) M)N) 
end. 
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red. 
eapply2 unequal_closed_normal_forms. 
eapply2 nf_abs. 
eapply2 lift_rec_preserves_normal. 
simpl. 
max_out. rewrite lift_rec_closed; try (split_all; omega). 
discriminate. 
eval_lamSF. eval_lamSF.
match goal with 
| |- _ _ (App _ ?N) _ => 
apply succ_red with (App (App N (left_component (Abs M2))) (right_component (Abs M2)))
end. 
eapply2 f_compound_lamSF_red. 
max_out. 
assert((exists o, M2 = Op o) \/ compound M2). eapply2 not_active_factorable. 
assert(status M2 <= maxvar M2) by eapply2 status_lt_maxvar. 
omega. 
inversion H0; split_all; subst; split_all. 
eval_lamSF. 
repeat (rewrite (subst_rec_closed equal_comb);  [| split_all]). 
unfold left_component, right_component. 
unfold_op; rewrite subst_rec_lift_rec; try omega. 
rewrite lift_rec_null. 
match goal with 
| |- multi_step lamSF_red1 (App (App _ ?M)?N) _ => 
apply transitive_red with (App (App (App k_op i_op) M)N) 
end. 
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red. 
eapply2 unequal_closed_normal_forms. 
discriminate. 
eval_lamSF. eval_lamSF.
rewrite subst_rec_lift_rec; try omega. 
rewrite subst_rec_lift_rec; try omega. 
rewrite subst_rec_lift_rec; try omega. 
rewrite lift_rec_null.
match goal with 
| |- multi_step lamSF_red1 (App (App _ ?M)?N) _ => 
apply transitive_red with (App (App (App k_op i_op) M)N) 
end. 
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red. 
eapply2 binds_rank; simpl; omega. 
eval_lamSF. eval_lamSF. 
eapply2 IHnor2. 
simpl in *; omega. 
max_out. 
eval_lamSF. eval_lamSF. auto. 
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
repeat (rewrite (subst_rec_closed equal_comb);  [| split_all]). 
unfold subst_rec; fold subst_rec. insert_Ref_out.
match goal with 
| |- multi_step lamSF_red1 (App (App _ ?M)?N) _ => 
apply transitive_red with (App (App k_op M)N) 
end. 
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red. 
eapply2 equal_closed_normal_forms. 
eval_lamSF. auto. 
(* 3 *) 
unfold binds. fixtac. fold binds. unfold binds_fn. eval_lamSF. 
repeat (rewrite (subst_rec_closed equal_comb);  [| split_all]). 
unfold subst_rec; fold subst_rec. insert_Ref_out.
rewrite lift_rec_preserves_star.
match goal with 
| |- multi_step lamSF_red1 (App (App _ ?M)?N) _ => 
apply transitive_red with (App (App (App k_op i_op) M)N) 
end. 
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red. 
rewrite lift_rec_null. 
eapply2 unequal_closed_normal_forms. 
eapply2 nf_abs. eapply2 normal_star. 
simpl. 
rewrite maxvar_star. omega. 
discriminate. 
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
repeat (rewrite (subst_rec_closed equal_comb);  [| split_all]). 
match goal with 
| |- multi_step lamSF_red1 (App (App _ ?M)?N) _ => 
apply transitive_red with (App (App (App k_op i_op) M)N) 
end. 
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red.
eapply2 unequal_closed_normal_forms. 
discriminate.
eval_lamSF; eval_lamSF. 
match goal with 
| |- multi_step lamSF_red1 (App (App _ ?M)?N) _ => 
apply transitive_red with (App (App (App k_op i_op) M)N) 
end. 
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red.
eapply2 binds_rank; simpl; omega.
eval_lamSF. eval_lamSF. 
eapply2 IHp.
assert(rank (star M) < rank (Abs M)) by eapply2 rank_star. 
omega. 
eapply2 normal_star. 
rewrite maxvar_star. auto. 
(* 2 *)

unfold binds. fixtac. fold binds. unfold binds_fn. eval_lamSF. 
repeat (rewrite (subst_rec_closed equal_comb);  [| split_all]). 
unfold subst_rec; fold subst_rec. insert_Ref_out.
rewrite subst_rec_lift_rec; [|split_all|split_all]. 
match goal with 
| |- multi_step lamSF_red1 (App (App _ ?M)?N) _ => 
apply transitive_red with (App (App (App k_op i_op) M)N) 
end. 
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red. 
rewrite lift_rec_null. rewrite lift_rec_null. 
eapply2 unequal_closed_normal_forms. 
simpl. 
assert(pred (max(maxvar M1) (maxvar M2)) = 0) by omega. 
rewrite max_pred in H1. 
auto. 
discriminate. 
eval_lamSF; eval_lamSF. 
eval_lamSF; eval_lamSF; auto. 
repeat (rewrite (subst_rec_closed equal_comb);  [| split_all]). 
unfold subst_rec; fold subst_rec. insert_Ref_out.
rewrite subst_rec_lift_rec; [|split_all|split_all]. 
match goal with 
| |- multi_step lamSF_red1 (App (App _ ?M)?N) _ => 
apply transitive_red with (App (App (App k_op i_op) M)N) 
end. 
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red. 
rewrite lift_rec_null.
eapply2 unequal_closed_normal_forms. 
simpl. 
assert(pred (max(maxvar M1) (maxvar M2)) = 0) by omega. 
rewrite max_pred in H1. 
max_out. 
discriminate. 
eval_lamSF; eval_lamSF. 
rewrite subst_rec_lift_rec; [|split_all|split_all]. 
rewrite subst_rec_lift_rec; [|split_all|split_all]. 
rewrite lift_rec_null.
(* 2 : Abs -> star *)
assert(maxvar M1 = 1 \/ maxvar M1 = 0). 
gen_case H0 (maxvar M1). 
gen_case H0 (maxvar M2). 
assert(max n n0 = 0) by omega. 
max_out. 
inversion H1. 
apply transitive_red with (App (App k_op k_op)  (App binds (Abs M2))).
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red.
unfold binds. fold lamSF_red. fixtac. fold binds. unfold binds_fn. eval_lamSF. 
repeat (rewrite (subst_rec_closed equal_comb);  [| split_all]). 
unfold subst_rec; fold subst_rec. insert_Ref_out.
match goal with 
| |- multi_step lamSF_red1 (App (App _ ?M)?N) _ => 
apply transitive_red with (App (App (App k_op i_op) M)N) 
end. 
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red.
eapply2 unequal_closed_normal_forms. 
eapply2 nf_compound. 
eapply2 nf_abs. 
eapply2 lift_rec_preserves_normal.
rewrite lift_rec_null. 
simpl. omega.  
discriminate. 
eval_lamSF; eval_lamSF. 
eval_lamSF; eval_lamSF. 
repeat (rewrite (subst_rec_closed equal_comb);  [| split_all]). 
unfold subst_rec; fold subst_rec. insert_Ref_out.
match goal with 
| |- multi_step lamSF_red1 (App (App _ ?M)?N) _ => 
apply transitive_red with (App (App (App k_op i_op) M)N) 
end. 
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red. 
eapply2 unequal_closed_normal_forms. 
discriminate. 
eval_lamSF. eval_lamSF.
rewrite subst_rec_lift_rec; try omega. 
rewrite subst_rec_lift_rec; try omega. 
rewrite subst_rec_lift_rec; try omega. 
rewrite lift_rec_null.
match goal with 
| |- multi_step lamSF_red1 (App (App _ ?M)?N) _ => 
apply transitive_red with (App (App (App k_op i_op) M)N) 
end. 
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red. 
eapply2 binds_rank. 
unfold_op; split_all; omega.  
eval_lamSF. eval_lamSF.
(* M1 *)  
unfold binds. fold lamSF_red. fixtac. fold binds. unfold binds_fn. eval_lamSF. 
repeat (rewrite (subst_rec_closed equal_comb);  [| split_all]). 
unfold subst_rec; fold subst_rec. insert_Ref_out.
match goal with 
| |- multi_step lamSF_red1 (App (App _ ?M)?N) _ => 
apply transitive_red with (App (App (App k_op i_op) M)N) 
end. 
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red. 
eapply2 unequal_closed_normal_forms. 
eapply2 nf_abs. 
eapply2 lift_rec_preserves_normal. 
simpl. 
rewrite lift_rec_null. 
omega. 
discriminate. 
eval_lamSF. eval_lamSF.
match goal with 
| |- _ _ (App _ ?N) _ => 
apply succ_red with (App (App N (left_component (Abs M1))) (right_component (Abs M1)))
end. 
eapply2 f_compound_lamSF_red.
assert((exists o, Abs M1 = Op o) \/ compound(Abs M1)). 
eapply2 not_active_factorable. 
simpl in *.  
assert(status M1 <= maxvar M1) by eapply2 status_lt_maxvar. 
omega. 
inversion H3; split_all; subst; split_all. 
eval_lamSF. 
repeat (rewrite (subst_rec_closed equal_comb);  [| split_all]). 
unfold left_component, right_component. 
unfold_op; rewrite subst_rec_lift_rec; try omega. 
rewrite lift_rec_null. 
match goal with 
| |- multi_step lamSF_red1 (App (App _ ?M)?N) _ => 
apply transitive_red with (App (App (App k_op i_op) M)N) 
end. 
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red. 
eapply2 unequal_closed_normal_forms. 
discriminate. 
eval_lamSF. eval_lamSF.
rewrite subst_rec_lift_rec; try omega. 
rewrite subst_rec_lift_rec; try omega. 
rewrite subst_rec_lift_rec; try omega. 
rewrite lift_rec_null.
match goal with 
| |- multi_step lamSF_red1 (App (App _ ?M)?N) _ => 
apply transitive_red with (App (App (App k_op i_op) M)N) 
end. 
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red. 
eapply2 binds_rank; simpl; omega.
eval_lamSF. eval_lamSF. 
eapply2 IHnor1. 
simpl in *; omega. 
eval_lamSF. auto. 
(* maxvar M1 = 0 *) 
apply transitive_red with (App (App (App k_op i_op) k_op)  (App binds (Abs M2))).
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red.
unfold binds. fold lamSF_red. fixtac. fold binds. unfold binds_fn. eval_lamSF. 
repeat (rewrite (subst_rec_closed equal_comb);  [| split_all]). 
unfold subst_rec; fold subst_rec. insert_Ref_out.
match goal with 
| |- multi_step lamSF_red1 (App (App _ ?M)?N) _ => 
apply transitive_red with (App (App (App k_op i_op) M)N) 
end. 
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red.
eapply2 unequal_closed_normal_forms. 
eapply2 nf_compound. 
eapply2 nf_abs. 
eapply2 lift_rec_preserves_normal.
rewrite lift_rec_null. 
simpl. omega.  
discriminate. 
eval_lamSF; eval_lamSF. 
eval_lamSF; eval_lamSF. 
repeat (rewrite (subst_rec_closed equal_comb);  [| split_all]). 
unfold subst_rec; fold subst_rec. insert_Ref_out.
match goal with 
| |- multi_step lamSF_red1 (App (App _ ?M)?N) _ => 
apply transitive_red with (App (App (App k_op i_op) M)N) 
end. 
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red. 
eapply2 unequal_closed_normal_forms. 
discriminate. 
eval_lamSF. eval_lamSF.
rewrite subst_rec_lift_rec; try omega. 
rewrite subst_rec_lift_rec; try omega. 
rewrite subst_rec_lift_rec; try omega. 
rewrite lift_rec_null.
match goal with 
| |- multi_step lamSF_red1 (App (App _ ?M)?N) _ => 
apply transitive_red with (App (App (App k_op i_op) M)N) 
end. 
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red. 
eapply2 binds_rank. 
unfold_op; split_all; omega.  
eval_lamSF. eval_lamSF.
(* M1 *)  
unfold binds. fold lamSF_red. fixtac. fold binds. unfold binds_fn. eval_lamSF. 
repeat (rewrite (subst_rec_closed equal_comb);  [| split_all]). 
unfold subst_rec; fold subst_rec. insert_Ref_out.
match goal with 
| |- multi_step lamSF_red1 (App (App _ ?M)?N) _ => 
apply transitive_red with (App (App (App k_op i_op) M)N) 
end. 
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red. 
eapply2 unequal_closed_normal_forms. 
eapply2 nf_abs. 
eapply2 lift_rec_preserves_normal. 
simpl. 
rewrite lift_rec_null. 
omega. 
discriminate. 
eval_lamSF. eval_lamSF.
match goal with 
| |- _ _ (App _ ?N) _ => 
apply succ_red with (App (App N (left_component (Abs M1))) (right_component (Abs M1)))
end. 
eapply2 f_compound_lamSF_red. 
assert((exists o, Abs M1 = Op o) \/ compound(Abs M1)). 
eapply2 not_active_factorable. 
simpl in *.  
assert(status M1 <= maxvar M1) by eapply2 status_lt_maxvar. 
omega. 
inversion H3; subst; split_all. 
eval_lamSF. 
repeat (rewrite (subst_rec_closed equal_comb);  [| split_all]). 
unfold left_component, right_component. 
unfold_op; rewrite subst_rec_lift_rec; try omega. 
rewrite lift_rec_null. 
match goal with 
| |- multi_step lamSF_red1 (App (App _ ?M)?N) _ => 
apply transitive_red with (App (App (App k_op i_op) M)N) 
end. 
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red. 
eapply2 unequal_closed_normal_forms. 
discriminate. 
eval_lamSF. eval_lamSF.
rewrite subst_rec_lift_rec; try omega. 
rewrite subst_rec_lift_rec; try omega. 
rewrite subst_rec_lift_rec; try omega. 
rewrite lift_rec_null.
match goal with 
| |- multi_step lamSF_red1 (App (App _ ?M)?N) _ => 
apply transitive_red with (App (App (App k_op i_op) M)N) 
end. 
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red. 
eapply2 binds_rank; simpl; omega.
eval_lamSF. eval_lamSF. 
eapply2 binds_star_0. 
eval_lamSF. eval_lamSF. 
(* now M2 *) 
rewrite H2 in H0. simpl in *. 
unfold binds. fold lamSF_red. fixtac. fold binds. unfold binds_fn. eval_lamSF. 
repeat (rewrite (subst_rec_closed equal_comb);  [| split_all]). 
unfold subst_rec; fold subst_rec. insert_Ref_out.
match goal with 
| |- multi_step lamSF_red1 (App (App _ ?M)?N) _ => 
apply transitive_red with (App (App (App k_op i_op) M)N) 
end. 
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red. 
eapply2 unequal_closed_normal_forms. 
eapply2 nf_abs. 
eapply2 lift_rec_preserves_normal. 
simpl. 
 rewrite lift_rec_closed; try (split_all; omega). 
discriminate. 
eval_lamSF. eval_lamSF.
match goal with 
| |- _ _ (App _ ?N) _ => 
apply succ_red with (App (App N (left_component (Abs M2))) (right_component (Abs M2)))
end. 
eapply2 f_compound_lamSF_red. 
assert((exists o, Abs M2 = Op o) \/ compound (Abs M2)). eapply2 not_active_factorable. 
assert(status (Abs M2) <= maxvar (Abs M2)) by eapply2 status_lt_maxvar. 
simpl in *. omega. 
inversion H3; split_all; subst; split_all. 
eval_lamSF. 
repeat (rewrite (subst_rec_closed equal_comb);  [| split_all]). 
unfold left_component, right_component. 
unfold_op; rewrite subst_rec_lift_rec; try omega. 
rewrite lift_rec_null. 
match goal with 
| |- multi_step lamSF_red1 (App (App _ ?M)?N) _ => 
apply transitive_red with (App (App (App k_op i_op) M)N) 
end. 
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red. 
eapply2 unequal_closed_normal_forms. 
discriminate. 
eval_lamSF. eval_lamSF.
rewrite subst_rec_lift_rec; try omega. 
rewrite subst_rec_lift_rec; try omega. 
rewrite subst_rec_lift_rec; try omega. 
rewrite lift_rec_null.
match goal with 
| |- multi_step lamSF_red1 (App (App _ ?M)?N) _ => 
apply transitive_red with (App (App (App k_op i_op) M)N) 
end. 
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red. 
eapply2 binds_rank; simpl; omega.
eval_lamSF. eval_lamSF. 
eapply2 IHnor2. 
simpl in *; omega. 
(* 1 *) 
unfold binds. fixtac. fold binds. unfold binds_fn. eval_lamSF. 
repeat (rewrite (subst_rec_closed equal_comb);  [| split_all]). 
unfold subst_rec; fold subst_rec. insert_Ref_out.
rewrite subst_rec_lift_rec; [|split_all|split_all]. 
match goal with 
| |- multi_step lamSF_red1 (App (App _ ?M)?N) _ => 
apply transitive_red with (App (App (App k_op i_op) M)N) 
end. 
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red. 
rewrite lift_rec_null. rewrite lift_rec_null. 
eapply2 unequal_closed_normal_forms. 
simpl. 
assert(pred (max(maxvar M1) (maxvar M2)) = 0) by omega. 
rewrite max_pred in H1. 
auto. 
discriminate. 
eval_lamSF; eval_lamSF. 
eval_lamSF; eval_lamSF; auto. 
repeat (rewrite (subst_rec_closed equal_comb);  [| split_all]). 
unfold subst_rec; fold subst_rec. insert_Ref_out.
rewrite subst_rec_lift_rec; [|split_all|split_all]. 
match goal with 
| |- multi_step lamSF_red1 (App (App _ ?M)?N) _ => 
apply transitive_red with (App (App (App k_op i_op) M)N) 
end. 
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red. 
rewrite lift_rec_null.
eapply2 unequal_closed_normal_forms. 
simpl. 
assert(pred (max(maxvar M1) (maxvar M2)) = 0) by omega. 
rewrite max_pred in H1. 
max_out. 
discriminate. 
eval_lamSF; eval_lamSF. 
rewrite subst_rec_lift_rec; [|split_all|split_all]. 
rewrite subst_rec_lift_rec; [|split_all|split_all]. 
rewrite lift_rec_null.
(* 2 : Abs -> star *)
assert(maxvar M1 = 1 \/ maxvar M1 = 0). 
gen_case H0 (maxvar M1). 
gen_case H0 (maxvar M2). 
assert(max n n0 = 0) by omega. 
max_out. 
inversion H1. 
apply transitive_red with (App (App k_op k_op)  (App binds (Abs M2))).
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red.
unfold binds. fold lamSF_red. fixtac. fold binds. unfold binds_fn. eval_lamSF. 
repeat (rewrite (subst_rec_closed equal_comb);  [| split_all]). 
unfold subst_rec; fold subst_rec. insert_Ref_out.
match goal with 
| |- multi_step lamSF_red1 (App (App _ ?M)?N) _ => 
apply transitive_red with (App (App (App k_op i_op) M)N) 
end. 
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red.
eapply2 unequal_closed_normal_forms. 
eapply2 nf_compound. 
eapply2 nf_abs. 
eapply2 lift_rec_preserves_normal.
rewrite lift_rec_null. 
simpl. omega.  
discriminate. 
eval_lamSF; eval_lamSF. 
eval_lamSF; eval_lamSF. 
repeat (rewrite (subst_rec_closed equal_comb);  [| split_all]). 
unfold subst_rec; fold subst_rec. insert_Ref_out.
match goal with 
| |- multi_step lamSF_red1 (App (App _ ?M)?N) _ => 
apply transitive_red with (App (App (App k_op i_op) M)N) 
end. 
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red. 
eapply2 unequal_closed_normal_forms. 
discriminate. 
eval_lamSF. eval_lamSF.
rewrite subst_rec_lift_rec; try omega. 
rewrite subst_rec_lift_rec; try omega. 
rewrite subst_rec_lift_rec; try omega. 
rewrite lift_rec_null.
match goal with 
| |- multi_step lamSF_red1 (App (App _ ?M)?N) _ => 
apply transitive_red with (App (App (App k_op i_op) M)N) 
end. 
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red. 
eapply2 binds_rank. 
unfold_op; split_all; omega.  
eval_lamSF. eval_lamSF.
(* M1 *)  
unfold binds. fold lamSF_red. fixtac. fold binds. unfold binds_fn. eval_lamSF. 
repeat (rewrite (subst_rec_closed equal_comb);  [| split_all]). 
unfold subst_rec; fold subst_rec. insert_Ref_out.
match goal with 
| |- multi_step lamSF_red1 (App (App _ ?M)?N) _ => 
apply transitive_red with (App (App (App k_op i_op) M)N) 
end. 
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red. 
eapply2 unequal_closed_normal_forms. 
eapply2 nf_abs. 
eapply2 lift_rec_preserves_normal. 
simpl. 
rewrite lift_rec_null. 
omega. 
discriminate. 
eval_lamSF. eval_lamSF.
match goal with 
| |- _ _ (App _ ?N) _ => 
apply succ_red with (App (App N (left_component (Abs M1))) (right_component (Abs M1)))
end. 
eapply2 f_compound_lamSF_red. 
inversion H; subst; split_all. 
eval_lamSF. 
repeat (rewrite (subst_rec_closed equal_comb);  [| split_all]). 
unfold left_component, right_component. 
unfold_op; rewrite subst_rec_lift_rec; try omega. 
rewrite lift_rec_null. 
match goal with 
| |- multi_step lamSF_red1 (App (App _ ?M)?N) _ => 
apply transitive_red with (App (App (App k_op i_op) M)N) 
end. 
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red. 
eapply2 unequal_closed_normal_forms. 
discriminate. 
eval_lamSF. eval_lamSF.
rewrite subst_rec_lift_rec; try omega. 
rewrite subst_rec_lift_rec; try omega. 
rewrite subst_rec_lift_rec; try omega. 
rewrite lift_rec_null.
match goal with 
| |- multi_step lamSF_red1 (App (App _ ?M)?N) _ => 
apply transitive_red with (App (App (App k_op i_op) M)N) 
end. 
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red. 
eapply2 binds_rank; simpl; omega.
eval_lamSF. eval_lamSF. 
eapply2 IHnor1. 
simpl in *; omega. 
eval_lamSF. auto. 
(* maxvar M1 = 0 *) 
apply transitive_red with (App (App (App k_op i_op) k_op)  (App binds (Abs M2))).
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red.
unfold binds. fold lamSF_red. fixtac. fold binds. unfold binds_fn. eval_lamSF. 
repeat (rewrite (subst_rec_closed equal_comb);  [| split_all]). 
unfold subst_rec; fold subst_rec. insert_Ref_out.
match goal with 
| |- multi_step lamSF_red1 (App (App _ ?M)?N) _ => 
apply transitive_red with (App (App (App k_op i_op) M)N) 
end. 
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red.
eapply2 unequal_closed_normal_forms. 
eapply2 nf_compound. 
eapply2 nf_abs. 
eapply2 lift_rec_preserves_normal.
rewrite lift_rec_null. 
simpl. omega.  
discriminate. 
eval_lamSF; eval_lamSF. 
eval_lamSF; eval_lamSF. 
repeat (rewrite (subst_rec_closed equal_comb);  [| split_all]). 
unfold subst_rec; fold subst_rec. insert_Ref_out.
match goal with 
| |- multi_step lamSF_red1 (App (App _ ?M)?N) _ => 
apply transitive_red with (App (App (App k_op i_op) M)N) 
end. 
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red. 
eapply2 unequal_closed_normal_forms. 
discriminate. 
eval_lamSF. eval_lamSF.
rewrite subst_rec_lift_rec; try omega. 
rewrite subst_rec_lift_rec; try omega. 
rewrite subst_rec_lift_rec; try omega. 
rewrite lift_rec_null.
match goal with 
| |- multi_step lamSF_red1 (App (App _ ?M)?N) _ => 
apply transitive_red with (App (App (App k_op i_op) M)N) 
end. 
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red. 
eapply2 binds_rank. 
unfold_op; split_all; omega.  
eval_lamSF. eval_lamSF.
(* M1 *)  
unfold binds. fold lamSF_red. fixtac. fold binds. unfold binds_fn. eval_lamSF. 
repeat (rewrite (subst_rec_closed equal_comb);  [| split_all]). 
unfold subst_rec; fold subst_rec. insert_Ref_out.
match goal with 
| |- multi_step lamSF_red1 (App (App _ ?M)?N) _ => 
apply transitive_red with (App (App (App k_op i_op) M)N) 
end. 
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red. 
eapply2 unequal_closed_normal_forms. 
eapply2 nf_abs. 
eapply2 lift_rec_preserves_normal. 
simpl. 
rewrite lift_rec_null. 
omega. 
discriminate. 
eval_lamSF. eval_lamSF.
match goal with 
| |- _ _ (App _ ?N) _ => 
apply succ_red with (App (App N (left_component (Abs M1))) (right_component (Abs M1)))
end. 
eapply2 f_compound_lamSF_red. 
inversion H; subst; split_all. 
eval_lamSF. 
repeat (rewrite (subst_rec_closed equal_comb);  [| split_all]). 
unfold left_component, right_component. 
unfold_op; rewrite subst_rec_lift_rec; try omega. 
rewrite lift_rec_null. 
match goal with 
| |- multi_step lamSF_red1 (App (App _ ?M)?N) _ => 
apply transitive_red with (App (App (App k_op i_op) M)N) 
end. 
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red. 
eapply2 unequal_closed_normal_forms. 
discriminate. 
eval_lamSF. eval_lamSF.
rewrite subst_rec_lift_rec; try omega. 
rewrite subst_rec_lift_rec; try omega. 
rewrite subst_rec_lift_rec; try omega. 
rewrite lift_rec_null.
match goal with 
| |- multi_step lamSF_red1 (App (App _ ?M)?N) _ => 
apply transitive_red with (App (App (App k_op i_op) M)N) 
end. 
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red. 
eapply2 binds_rank; simpl; omega.
eval_lamSF. eval_lamSF. 
eapply2 binds_star_0. 
eval_lamSF. eval_lamSF. 
(* now M2 *) 
rewrite H2 in H0. simpl in *. 
unfold binds. fold lamSF_red. fixtac. fold binds. unfold binds_fn. eval_lamSF. 
repeat (rewrite (subst_rec_closed equal_comb);  [| split_all]). 
unfold subst_rec; fold subst_rec. insert_Ref_out.
match goal with 
| |- multi_step lamSF_red1 (App (App _ ?M)?N) _ => 
apply transitive_red with (App (App (App k_op i_op) M)N) 
end. 
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red. 
eapply2 unequal_closed_normal_forms. 
eapply2 nf_abs. 
eapply2 lift_rec_preserves_normal. 
simpl. 
 rewrite lift_rec_closed; try (split_all; omega). 
discriminate. 
eval_lamSF. eval_lamSF.
match goal with 
| |- _ _ (App _ ?N) _ => 
apply succ_red with (App (App N (left_component (Abs M2))) (right_component (Abs M2)))
end. 
eapply2 f_compound_lamSF_red. 
assert((exists o, Abs M2 = Op o) \/ compound (Abs M2)). eapply2 not_active_factorable. 
assert(status (Abs M2) <= maxvar (Abs M2)) by eapply2 status_lt_maxvar. 
simpl in *. omega. 
inversion H3; split_all; subst; split_all. 
eval_lamSF. 
repeat (rewrite (subst_rec_closed equal_comb);  [| split_all]). 
unfold left_component, right_component. 
unfold_op; rewrite subst_rec_lift_rec; try omega. 
rewrite lift_rec_null. 
match goal with 
| |- multi_step lamSF_red1 (App (App _ ?M)?N) _ => 
apply transitive_red with (App (App (App k_op i_op) M)N) 
end. 
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red. 
eapply2 unequal_closed_normal_forms. 
discriminate. 
eval_lamSF. eval_lamSF.
rewrite subst_rec_lift_rec; try omega. 
rewrite subst_rec_lift_rec; try omega. 
rewrite subst_rec_lift_rec; try omega. 
rewrite lift_rec_null.
match goal with 
| |- multi_step lamSF_red1 (App (App _ ?M)?N) _ => 
apply transitive_red with (App (App (App k_op i_op) M)N) 
end. 
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red. 
eapply2 binds_rank; simpl; omega.
eval_lamSF. eval_lamSF. 
eapply2 IHnor2. 
simpl in *; omega. 
Qed. 
