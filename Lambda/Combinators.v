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
(*                    Combinators.v                                   *)
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


Ltac eval_lamSF := eval_lamSF0;  relocate_lt; unfold subst; unfold subst_rec; fold subst_rec; insert_Ref_out; repeat (rewrite lift_rec_null). 

Definition abs_K := Abs (Abs (Ref 1)). 
Definition abs_S := 
Abs(Abs (Abs (App (App (Ref 2) (Ref 0)) (App (Ref 1) (Ref 0))))). 



Inductive combinator : lamSF -> Prop := 
| comb_op : forall o, combinator (Op o)
| comb_app : forall M N, combinator M -> combinator N -> combinator (App M N)
.

Hint Resolve comb_op comb_app. 

Lemma combinator_decidable: forall M, combinator M \/ (combinator M -> False).
Proof. induction M. 
right; intro c; inversion c. 
left; split_all. 
right; intro c; inversion c. 
inversion IHM1. 
inversion IHM2. 
left; split_all. 
right; intro c; inversion c; split_all. 
right; intro c; inversion c; split_all. 
Qed. 


Definition star_comb := Abs (App (App (App f_op (App abs_K (Ref 0))) k_op) (App k_op i_op)). 

Lemma star_comb_star : forall M, normal M -> maxvar M = 0 -> lamSF_red (App star_comb M) (star M).
Proof. 
intros M nor; unfold star_comb; split_all; eval_lamSF. 
unfold abs_K. unfold subst_rec; fold subst_rec. insert_Ref_out. 
apply succ_red with 
(App
        (App (App (Op Fop) (subst M (Abs (Ref 1))))
           (App (Op Fop) (Op Fop)))
        (App (App (Op Fop) (Op Fop))
           (App (App (Op Sop) (App (Op Fop) (Op Fop)))
              (App (Op Fop) (Op Fop))))) .
eapply2 appl_lamSF_red. 
unfold subst; unfold subst_rec; fold subst_rec. insert_Ref_out. 
rewrite lift_rec_closed; try omega. 
apply succ_red with (App (App (App k_op i_op) (left_component (Abs M))) (right_component (Abs M))). 
eapply2 f_compound_lamSF_red. 
assert((exists o, Abs M = Op o) \/ compound (Abs M)). 
eapply2 not_active_factorable. 
assert(status (Abs M) <= maxvar (Abs M)) by eapply2 status_lt_maxvar. 
simpl in *; omega. 
inversion H0. 
split_all; discriminate. 
auto. 
eval_lamSF. eval_lamSF. split_all. 
Qed. 

Lemma maxvar_combinator : forall M, combinator M -> maxvar M = 0.
Proof. intros M comb; induction comb; split_all. rewrite IHcomb1; rewrite IHcomb2; auto. Qed. 


Definition is_comb_fn := Abs (Abs 
(App (App (App f_op (Ref 0)) k_op) (Abs (Abs 
(App (App (App (App equal_comb abs_left) (Ref 1)) (App k_op i_op))
(App (App (App (Ref 3) (Ref 1)) (App (Ref 3) (Ref 0))) (App k_op i_op))
))))).

Definition is_comb := App fixpoint is_comb_fn. 

Lemma is_comb_true: forall M, normal M -> combinator M -> lamSF_red (App is_comb M) k_op. 
Proof. 
intros M nor comb; induction nor; inversion comb; split_all. 
(* 3 *) 
unfold is_comb.  fixtac. fold is_comb. unfold is_comb_fn. 
eval_lamSF.
unfold subst_rec; fold subst_rec. insert_Ref_out.
eval_lamSF. auto. 
(* 2 *) 
assert(status (App M1 M2) <= maxvar (App M1 M2)) by eapply2 status_lt_maxvar. 
assert(maxvar (App M1 M2) = 0) by eapply2 maxvar_combinator. 
noway. 
(* 1 *) 
unfold is_comb.  fixtac. fold is_comb. unfold is_comb_fn. 
eval_lamSF.
unfold subst_rec; fold subst_rec. insert_Ref_out.
rewrite lift_rec_null.
rewrite lift_rec_null.
repeat (rewrite (subst_rec_closed equal_comb);  [| split_all]). 
rewrite subst_rec_lift_rec; try (split_all; omega). 
rewrite lift_rec_closed; try (split_all; omega). 
match goal with 
| |- multi_step lamSF_red1 (App _ ?N) _ => 
apply succ_red with (App (App N (left_component (App M1 M2))) (right_component (App M1 M2)))
end. 
eapply2 f_compound_lamSF_red. 
eval_lamSF.
repeat (rewrite (subst_rec_closed equal_comb);  [| split_all]). 
unfold left_component, right_component. 
rewrite subst_rec_lift_rec; try (split_all; omega). 
rewrite lift_rec_null.
match goal with 
| |- multi_step lamSF_red1 (App (App _ ?M)?N) _ => 
apply transitive_red with (App (App (App k_op i_op) M)N) 
end. 
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red. 
eapply2 unequal_closed_normal_forms. 
eapply2 maxvar_combinator. 
inversion H; discriminate. 
eval_lamSF. eval_lamSF. 
repeat (rewrite subst_rec_closed; try (split_all; omega)). 
apply transitive_red with (App (App k_op k_op) (App k_op i_op)). 
eapply2 preserves_app_lamSF_red. 
repeat eval_lamSF. auto. 
Qed. 

Lemma is_comb_false: forall M, normal M -> maxvar M = 0 -> (combinator M -> False) -> lamSF_red (App is_comb M) (App k_op i_op). 
Proof. 
intros M nor; induction nor; split_all. 
(* 4 *) 
assert False by eapply2 H0. noway. 
(* 3 *) 
unfold is_comb.  fixtac. fold is_comb. unfold is_comb_fn. 
eval_lamSF.
unfold subst_rec; fold subst_rec. insert_Ref_out.
rewrite lift_rec_null. 
match goal with 
| |- multi_step lamSF_red1 (App _ ?N) _ => 
apply succ_red with (App (App N (left_component (Abs M))) (right_component (Abs M)))
end. 
eapply2 f_compound_lamSF_red. 
assert((exists o, Abs M = Op o) \/ compound(Abs M)). 
eapply2 not_active_factorable. 
assert(status (Abs M) <= maxvar(Abs M)) by eapply2 status_lt_maxvar. 
simpl in *. 
omega. 
inversion H1; split_all; subst; split_all. 
eval_lamSF.
repeat (rewrite (subst_rec_closed equal_comb);  [| split_all]). 
rewrite subst_rec_lift_rec; try (split_all; omega). 
rewrite lift_rec_null.
unfold left_component, right_component. unfold_op.  
match goal with 
| |- multi_step lamSF_red1 (App (App _ ?M)?N) _ => 
apply transitive_red with (App (App k_op M)N) 
end. 
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red. 
eapply2 equal_closed_normal_forms. 
eval_lamSF. auto. 
(* 2 *) 
assert(status (App M1 M2) <= maxvar (App M1 M2)) by eapply2 status_lt_maxvar. 
unfold maxvar in *; fold maxvar in *. 
noway. 
(* 1 *) 
unfold is_comb.  fixtac. fold is_comb. unfold is_comb_fn. 
eval_lamSF.
unfold subst_rec; fold subst_rec. insert_Ref_out.
rewrite lift_rec_null.
rewrite lift_rec_null.
repeat (rewrite (subst_rec_closed equal_comb);  [| split_all]). 
rewrite subst_rec_lift_rec; try (split_all; omega). 
rewrite lift_rec_closed; try (split_all; omega). 
match goal with 
| |- multi_step lamSF_red1 (App _ ?N) _ => 
apply succ_red with (App (App N (left_component (App M1 M2))) (right_component (App M1 M2)))
end. 
eapply2 f_compound_lamSF_red. 
eval_lamSF.
repeat (rewrite (subst_rec_closed equal_comb);  [| split_all]). 
unfold left_component, right_component. 
rewrite subst_rec_lift_rec; try (split_all; omega). 
rewrite lift_rec_null.
match goal with 
| |- multi_step lamSF_red1 (App (App _ ?M)?N) _ => 
apply transitive_red with (App (App (App k_op i_op) M)N) 
end. 
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red. 
eapply2 unequal_closed_normal_forms. 
max_out. 
inversion H; discriminate. 
eval_lamSF. eval_lamSF. 
repeat (rewrite subst_rec_closed; try (split_all; omega)). 
assert(combinator M1 \/ (combinator M1 -> False)) by eapply2 combinator_decidable. 
inversion H2. 
assert(combinator M2 \/ (combinator M2 -> False)) by eapply2 combinator_decidable. 
inversion H4. 
assert False. eapply2 H1. noway. 
apply transitive_red with (App (App k_op (App k_op i_op)) (App k_op i_op)). 
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red. 
eapply2 is_comb_true. 
eapply2 IHnor2. 
max_out. 
repeat (eval_lamSF); auto.

apply transitive_red with (App (App (App k_op i_op) (App is_comb M2)) (App k_op i_op)). 
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red. 
eapply2 IHnor1. 
max_out. 
repeat (eval_lamSF); auto. 
Qed. 

