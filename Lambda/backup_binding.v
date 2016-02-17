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


Ltac eval_lamSF := eval_lamSF0;  relocate_lt; unfold subst; unfold subst_rec; fold subst_rec; insert_Ref_out; repeat (rewrite lift_rec_null). 

Definition abs_K := Abs (Abs (Ref 1)). 
Definition abs_S := 
Abs(Abs (Abs (App (App (Ref 2) (Ref 0)) (App (Ref 1) (Ref 0))))). 



Inductive combinator : lambda -> Prop := 
| comb_op : forall o, combinator (Op o)
| comb_app : forall M N, combinator M -> combinator N -> combinator (App M N)
.

Hint Resolve comb_op comb_app. 


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




(* has_combinator M N := 
if M = N then K else 
match N with 
| o => KI
| N1 N2 => has_combinator M N1 \/ has_combinator M N2 

*) 

Lemma maxvar_combinator : forall M, combinator M -> maxvar M = 0.
Proof. intros M comb; induction comb; split_all. rewrite IHcomb1; rewrite IHcomb2; auto. Qed. 


Definition has_combinator_fn := Abs (Abs (Abs 
(App (App (App (App equal_comb (Ref 1)) (Ref 0)) k_op) 
(App (App (App f_op (Ref 0)) (App k_op i_op)) (Abs (Abs 
(App (App (App (App (Ref 4) (Ref 3)) (Ref 1)) k_op) 
(App (App (Ref 4) (Ref 3)) (Ref 0))
))))))).

Definition has_combinator := App fixpoint has_combinator_fn. 

Lemma has_combinator_self : forall M, normal M -> maxvar M = 0 -> lamSF_red (App (App has_combinator M) M) k_op. 
Proof. 
split_all. 
unfold has_combinator.  
apply transitive_red with (App (App (App has_combinator_fn (App fixpoint has_combinator_fn)) M) M). 
eapply2 preserves_app_lamSF_red. 
fixtac. auto. 
fold has_combinator. unfold has_combinator_fn. 
eval_lamSF. 
repeat (rewrite (subst_rec_closed equal_comb);  [| split_all]). 
unfold subst_rec; fold subst_rec. insert_Ref_out.
rewrite subst_rec_lift_rec; [|split_all|split_all]. 
rewrite lift_rec_null.
unfold subst_rec; fold subst_rec. insert_Ref_out. rewrite lift_rec_null. 
match goal with 
| |- multi_step lamSF_red1 (App (App _ ?M)?N) _ => 
apply transitive_red with (App (App k_op M)N) 
end. 
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red. 
eapply2 equal_closed_normal_forms. 
eval_lamSF.  auto. 
Qed. 

Lemma has_combinator_rank : forall M, combinator M -> normal M -> forall N, normal N -> maxvar N = 0 -> rank M > rank N -> rank M > rank (id s_op) -> 
lamSF_red (App (App has_combinator M) N) (App k_op i_op).
Proof. 
cut(forall p M, combinator M -> normal M -> forall N, rank N <= p -> normal N -> maxvar N = 0 -> rank M > rank N -> rank M > rank (id s_op) -> 
lamSF_red (App (App has_combinator M) N) (App k_op i_op)).
split_all. 
eapply2 H. 
induction p. 
split_all. 
assert(rank N >0) by eapply2 rank_positive. 
noway. 
(* p > 0 *) 
intros M rnk comb nor_M N nor; induction nor; split_all. 
(* 4 *) 
unfold has_combinator.  
fixtac. fold has_combinator. unfold has_combinator_fn. 
eval_lamSF. 
repeat (rewrite (subst_rec_closed equal_comb);  [| split_all]). 
unfold subst_rec; fold subst_rec. insert_Ref_out.
rewrite subst_rec_lift_rec; [|split_all|split_all]. 
rewrite subst_rec_lift_rec; [|split_all|split_all]. 
unfold subst_rec; fold subst_rec. insert_Ref_out.
rewrite subst_rec_lift_rec; [|split_all|split_all]. 
rewrite subst_rec_lift_rec; [|split_all|split_all]. 
rewrite lift_rec_null.
match goal with 
| |- multi_step lamSF_red1 (App (App _ ?M)?N) _ => 
apply transitive_red with (App (App (App k_op i_op) M)N) 
end. 
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red. 
eapply2 unequal_closed_normal_forms.
eapply2 maxvar_combinator. 
intro. subst. 
simpl in *. noway. 
eval_lamSF. eval_lamSF.  
eval_lamSF. auto.
(* 3 *) 
unfold has_combinator.  
fixtac. fold has_combinator. unfold has_combinator_fn. 
eval_lamSF. 
repeat (rewrite (subst_rec_closed equal_comb);  [| split_all]). 
unfold subst_rec; fold subst_rec. insert_Ref_out.
rewrite subst_rec_lift_rec; [|split_all|split_all]. 
rewrite subst_rec_lift_rec; [|split_all|split_all]. 
unfold subst_rec; fold subst_rec. insert_Ref_out.
rewrite subst_rec_lift_rec; [|split_all|split_all]. 
rewrite subst_rec_lift_rec; [|split_all|split_all]. 
rewrite lift_rec_null.
match goal with 
| |- multi_step lamSF_red1 (App (App _ ?M)?N) _ => 
apply transitive_red with (App (App (App k_op i_op) M)N) 
end. 
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red. 
rewrite lift_rec_null. 
eapply2 unequal_closed_normal_forms.
eapply2 maxvar_combinator. 
intro. subst. 
simpl in *. noway. 
eval_lamSF. eval_lamSF.  
match goal with 
| |- _ _ (App _ ?N) _ => 
apply succ_red with (App (App N (left_component (Abs M0))) (right_component (Abs M0)))
end.
eapply2 f_compound_lamSF_red. 
assert((exists o, Abs M0 = Op o) \/  compound(Abs M0)). 
eapply2 not_active_factorable. 
assert(status (Abs M0) <= maxvar (Abs M0)) by eapply2 status_lt_maxvar. 
simpl in *. omega. 
inversion H2; split_all. 
eval_lamSF. 
rewrite subst_rec_lift_rec; [|split_all|split_all]. 
rewrite subst_rec_lift_rec; [|split_all|split_all]. 
unfold subst_rec; fold subst_rec. insert_Ref_out.
rewrite subst_rec_lift_rec; [|split_all|split_all]. 
rewrite subst_rec_lift_rec; [|split_all|split_all]. 
rewrite lift_rec_null.
rewrite lift_rec_null.
rewrite subst_rec_lift_rec; [|split_all|split_all]. 
rewrite lift_rec_null.
rewrite lift_rec_null.
unfold left_component, right_component. 
match goal with 
| |- multi_step lamSF_red1 (App (App _ ?M)?N) _ => 
apply transitive_red with (App (App (App k_op i_op) M)N) 
end. 
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red. 
unfold has_combinator.  
fixtac. fold has_combinator. unfold has_combinator_fn. 
eval_lamSF. 
repeat (rewrite (subst_rec_closed equal_comb);  [| split_all]). 
unfold subst_rec; fold subst_rec. insert_Ref_out.
rewrite subst_rec_lift_rec; [|split_all|split_all]. 
rewrite subst_rec_lift_rec; [|split_all|split_all]. 
unfold subst_rec; fold subst_rec. insert_Ref_out.
rewrite subst_rec_lift_rec; [|split_all|split_all]. 
rewrite subst_rec_lift_rec; [|split_all|split_all]. 
rewrite lift_rec_null.
match goal with 
| |- multi_step lamSF_red1 (App (App _ ?M)?N) _ => 
apply transitive_red with (App (App (App k_op i_op) M)N) 
end. 
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red. 
eapply2 unequal_closed_normal_forms.
eapply2 maxvar_combinator. 
intro. subst. 
simpl in *. noway. 
eval_lamSF. eval_lamSF.  
eval_lamSF. eval_lamSF.  
rewrite subst_rec_lift_rec; [|split_all|split_all]. 
rewrite subst_rec_lift_rec; [|split_all|split_all]. 
unfold subst_rec; fold subst_rec. insert_Ref_out.
rewrite subst_rec_lift_rec; [|split_all|split_all]. 
rewrite subst_rec_lift_rec; [|split_all|split_all]. 
rewrite lift_rec_null.
rewrite lift_rec_null.
match goal with 
| |- multi_step lamSF_red1 (App (App _ ?M)?N) _ => 
apply transitive_red with (App (App (App k_op i_op) M)N) 
end. 
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red. 
unfold has_combinator.  
fixtac. fold has_combinator. unfold has_combinator_fn. 
eval_lamSF. 
repeat (rewrite (subst_rec_closed equal_comb);  [| split_all]). 
unfold subst_rec; fold subst_rec. insert_Ref_out.
rewrite subst_rec_lift_rec; [|split_all|split_all]. 
rewrite subst_rec_lift_rec; [|split_all|split_all]. 
unfold subst_rec; fold subst_rec. insert_Ref_out.
rewrite subst_rec_lift_rec; [|split_all|split_all]. 
rewrite subst_rec_lift_rec; [|split_all|split_all]. 
rewrite lift_rec_null.
match goal with 
| |- multi_step lamSF_red1 (App (App _ ?M)?N) _ => 
apply transitive_red with (App (App (App k_op i_op) M)N) 
end. 
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red. 
eapply2 unequal_closed_normal_forms.
eapply2 maxvar_combinator. 
intro. subst. 
simpl in *. noway. 
eval_lamSF. eval_lamSF.  
eval_lamSF. eval_lamSF.  
rewrite subst_rec_lift_rec; [|split_all|split_all]. 
rewrite subst_rec_lift_rec; [|split_all|split_all]. 
unfold subst_rec; fold subst_rec. insert_Ref_out.
rewrite subst_rec_lift_rec; [|split_all|split_all]. 
rewrite subst_rec_lift_rec; [|split_all|split_all]. 
rewrite lift_rec_null.
rewrite lift_rec_null.
match goal with 
| |- multi_step lamSF_red1 (App (App _ ?M)?N) _ => 
apply transitive_red with (App (App (App k_op i_op) M)N) 
end. 
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red. 
unfold has_combinator.  
fixtac. fold has_combinator. unfold has_combinator_fn. 
eval_lamSF. 
repeat (rewrite (subst_rec_closed equal_comb);  [| split_all]). 
unfold subst_rec; fold subst_rec. insert_Ref_out.
rewrite subst_rec_lift_rec; [|split_all|split_all]. 
rewrite subst_rec_lift_rec; [|split_all|split_all]. 
unfold subst_rec; fold subst_rec. insert_Ref_out.
rewrite subst_rec_lift_rec; [|split_all|split_all]. 
rewrite subst_rec_lift_rec; [|split_all|split_all]. 
rewrite lift_rec_null.
match goal with 
| |- multi_step lamSF_red1 (App (App _ ?M)?N) _ => 
apply transitive_red with (App (App (App k_op i_op) M)N) 
end. 
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red. 
eapply2 unequal_closed_normal_forms.
eapply2 maxvar_combinator. 
intro. subst. 
simpl in *. noway. 
eval_lamSF. eval_lamSF.  
eval_lamSF. auto.
eval_lamSF. eval_lamSF. 
unfold has_combinator.  fold lamSF_red. 
fixtac. fold has_combinator. unfold has_combinator_fn. 
eval_lamSF. 
repeat (rewrite (subst_rec_closed equal_comb);  [| split_all]). 
unfold subst_rec; fold subst_rec. insert_Ref_out.
rewrite subst_rec_lift_rec; [|split_all|split_all]. 
rewrite subst_rec_lift_rec; [|split_all|split_all]. 
unfold subst_rec; fold subst_rec. insert_Ref_out.
rewrite subst_rec_lift_rec; [|split_all|split_all]. 
rewrite subst_rec_lift_rec; [|split_all|split_all]. 
rewrite lift_rec_null.
match goal with 
| |- multi_step lamSF_red1 (App (App _ ?M)?N) _ => 
apply transitive_red with (App (App (App k_op i_op) M)N) 
end. 
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red. 
eapply2 unequal_closed_normal_forms.
eapply2 maxvar_combinator. 
intro. subst. 
simpl in *. noway. 
eval_lamSF. eval_lamSF.  
eval_lamSF. eval_lamSF. 
unfold subst_rec; fold subst_rec. insert_Ref_out.
rewrite subst_rec_lift_rec; [|split_all|split_all]. 
rewrite subst_rec_lift_rec; [|split_all|split_all]. 
rewrite subst_rec_lift_rec; [|split_all|split_all]. 
rewrite subst_rec_lift_rec; [|split_all|split_all]. 
rewrite lift_rec_null.
rewrite lift_rec_null.
match goal with 
| |- multi_step lamSF_red1 (App (App _ ?M)?N) _ => 
apply transitive_red with (App (App (App k_op i_op) M)N) 
end. 
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red. 
unfold has_combinator.  fold lamSF_red. 
fixtac. fold has_combinator. unfold has_combinator_fn. 
eval_lamSF. 
repeat (rewrite (subst_rec_closed equal_comb);  [| split_all]). 
unfold subst_rec; fold subst_rec. insert_Ref_out.
rewrite subst_rec_lift_rec; [|split_all|split_all]. 
rewrite subst_rec_lift_rec; [|split_all|split_all]. 
unfold subst_rec; fold subst_rec. insert_Ref_out.
rewrite subst_rec_lift_rec; [|split_all|split_all]. 
rewrite subst_rec_lift_rec; [|split_all|split_all]. 
rewrite lift_rec_null.
match goal with 
| |- multi_step lamSF_red1 (App (App _ ?M)?N) _ => 
apply transitive_red with (App (App (App k_op i_op) M)N) 
end. 
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red. 
eapply2 unequal_closed_normal_forms.
eapply2 maxvar_combinator. 
intro. subst. 
simpl in *. noway. 
eval_lamSF. eval_lamSF.  
eval_lamSF. auto. 
eval_lamSF. eval_lamSF. 
unfold has_combinator.  fold lamSF_red. 
fixtac. fold has_combinator. unfold has_combinator_fn. 
eval_lamSF. 
repeat (rewrite (subst_rec_closed equal_comb);  [| split_all]). 
unfold subst_rec; fold subst_rec. insert_Ref_out.
rewrite subst_rec_lift_rec; [|split_all|split_all]. 
rewrite subst_rec_lift_rec; [|split_all|split_all]. 
unfold subst_rec; fold subst_rec. insert_Ref_out.
rewrite subst_rec_lift_rec; [|split_all|split_all]. 
rewrite subst_rec_lift_rec; [|split_all|split_all]. 
rewrite lift_rec_null.
match goal with 
| |- multi_step lamSF_red1 (App (App _ ?M)?N) _ => 
apply transitive_red with (App (App (App k_op i_op) M)N) 
end. 
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red. 
eapply2 unequal_closed_normal_forms.
eapply2 maxvar_combinator. 
intro. subst. 
simpl in *. noway. 
eval_lamSF. eval_lamSF.  
eval_lamSF. auto. 
eval_lamSF. eval_lamSF. 
unfold has_combinator.  fold lamSF_red. 
fixtac. fold has_combinator. unfold has_combinator_fn. 
eval_lamSF. 
repeat (rewrite (subst_rec_closed equal_comb);  [| split_all]). 
unfold subst_rec; fold subst_rec. insert_Ref_out.
rewrite subst_rec_lift_rec; [|split_all|split_all]. 
rewrite subst_rec_lift_rec; [|split_all|split_all]. 
unfold subst_rec; fold subst_rec. insert_Ref_out.
rewrite subst_rec_lift_rec; [|split_all|split_all]. 
rewrite subst_rec_lift_rec; [|split_all|split_all]. 
rewrite lift_rec_null.
match goal with 
| |- multi_step lamSF_red1 (App (App _ ?M)?N) _ => 
apply transitive_red with (App (App (App k_op i_op) M)N) 
end. 
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red. 
eapply2 unequal_closed_normal_forms.
eapply2 maxvar_combinator. 
intro. subst. 
simpl in *. noway. 
eval_lamSF. eval_lamSF.  
eval_lamSF. auto. 
eval_lamSF. eval_lamSF. 
eapply2 IHp. 
assert(rank (star M0) < rank (Abs M0)) by eapply2 rank_star. 
omega. 
eapply2 normal_star. 
rewrite maxvar_star. auto. 
assert(rank (star M0) < rank (Abs M0)) by eapply2 rank_star. simpl in *; omega. 
(* 2 *) 
assert(status (App M1 M2) <= maxvar (App M1 M2)) by eapply2 status_lt_maxvar. 
simpl in *. noway. 
(* 1 *) 
unfold has_combinator.  
fixtac. fold has_combinator. unfold has_combinator_fn. 
eval_lamSF. 
repeat (rewrite (subst_rec_closed equal_comb);  [| split_all]). 
unfold subst_rec; fold subst_rec. insert_Ref_out.
rewrite subst_rec_lift_rec; [|split_all|split_all]. 
rewrite subst_rec_lift_rec; [|split_all|split_all]. 
unfold subst_rec; fold subst_rec. insert_Ref_out.
rewrite subst_rec_lift_rec; [|split_all|split_all]. 
rewrite subst_rec_lift_rec; [|split_all|split_all]. 
rewrite lift_rec_null.
rewrite lift_rec_null.
rewrite lift_rec_null.
match goal with 
| |- multi_step lamSF_red1 (App (App _ ?M)?N) _ => 
apply transitive_red with (App (App (App k_op i_op) M)N) 
end. 
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red. 
eapply2 unequal_closed_normal_forms.
eapply2 maxvar_combinator. 
intro. subst. 
simpl in *. noway. 
eval_lamSF. eval_lamSF. 
match goal with 
| |- _ _ (App _ ?N) _ => 
apply succ_red with (App (App N (left_component (App M1 M2))) (right_component (App M1 M2)))
end.
eapply2 f_compound_lamSF_red.
eval_lamSF.  
rewrite subst_rec_lift_rec; [|split_all|split_all]. 
rewrite subst_rec_lift_rec; [|split_all|split_all]. 
unfold subst_rec; fold subst_rec. insert_Ref_out.
rewrite subst_rec_lift_rec; [|split_all|split_all]. 
rewrite subst_rec_lift_rec; [|split_all|split_all]. 
rewrite lift_rec_null.
rewrite lift_rec_null.
rewrite subst_rec_lift_rec; [|split_all|split_all]. 
rewrite lift_rec_null.
rewrite lift_rec_null.
unfold left_component, right_component. 
match goal with 
| |- multi_step lamSF_red1 (App (App _ ?M)?N) _ => 
apply transitive_red with (App (App (App k_op i_op) M)N) 
end. 
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red. 
eapply2 IHnor1. 
simpl in *. omega.  max_out. omega. 
eval_lamSF. eval_lamSF. 
eapply2 IHnor2. 
simpl in *. omega.  max_out. omega. 
Qed. 


Lemma has_combinator_i_op_star : forall M, normal M -> maxvar M = 0 -> 
lamSF_red (App (App has_combinator i_op) (star M)) (App k_op i_op). 
Proof. 
cut(forall p M, rank M <= p -> normal M -> maxvar M = 0 -> 
lamSF_red (App (App has_combinator i_op) (star M)) (App k_op i_op)). 
split_all. 
eapply2 H. 
induction p. 
split_all. 
assert(rank M >0) by eapply2 rank_positive; noway. 
(* p > 0 *) 
intros M rnk nor; induction nor; split_all. 
(* 4 *)
unfold_op; eapply2 has_combinator_rank; simpl; omega. 
(* 3 *) 
unfold has_combinator.  
fixtac. fold has_combinator. unfold has_combinator_fn. 
eval_lamSF. 
repeat (rewrite (subst_rec_closed equal_comb);  [| split_all]). 
unfold subst_rec; fold subst_rec. insert_Ref_out.
rewrite subst_rec_lift_rec; [|split_all|split_all]. 
rewrite lift_rec_closed.
2: split_all; omega. 
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
eapply2 normal_star. 
simpl. 
rewrite lift_rec_null. assert(maxvar (star M) = pred (maxvar M)) by eapply2 maxvar_star. 
omega. 
discriminate. 
eval_lamSF. eval_lamSF.
repeat(rewrite (subst_rec_closed has_combinator); try (split_all; omega)). 
match goal with 
| |- _ _ (App _ ?N) _ => 
apply succ_red with (App (App N (left_component (Abs (star M)))) (right_component (Abs (star M))))
end. 
eapply2 f_compound_lamSF_red. 
eapply2 abs_compound_compound. 
eapply2 star_compound. 
eval_lamSF.  
repeat (rewrite (subst_rec_closed has_combinator);  [| split_all]). 
unfold left_component, right_component. 
unfold_op. rewrite subst_rec_lift_rec; try omega. rewrite lift_rec_null. 
match goal with 
| |- multi_step lamSF_red1 (App (App _ ?M)?N) _ => 
apply transitive_red with (App (App (App k_op i_op) M)N) 
end. 
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red.
eapply2 has_combinator_rank; simpl; omega. 
eval_lamSF. eval_lamSF. 
eapply2 IHp.
assert(rank (star M) < rank (Abs M)) by eapply2 rank_star. 
omega. 
eapply2 normal_star. 
rewrite maxvar_star. 
omega. 
(* 2 *)
assert(status (App M1 M2) <= maxvar (App M1 M2)) by eapply2 status_lt_maxvar. 
simpl in *. noway.  
(* 1 *) 
unfold has_combinator. 
fixtac. fold has_combinator. unfold has_combinator_fn. 
eval_lamSF. 
repeat (rewrite (subst_rec_closed equal_comb);  [| split_all]). 
unfold subst_rec; fold subst_rec. insert_Ref_out.
rewrite subst_rec_lift_rec; [|split_all|split_all]. 
rewrite lift_rec_closed.
2: split_all; omega. 
unfold subst_rec; fold subst_rec. insert_Ref_out. 
match goal with 
| |- multi_step lamSF_red1 (App (App _ ?M)?N) _ => 
apply transitive_red with (App (App (App k_op i_op) M)N) 
end. 
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red. 
rewrite lift_rec_null. 
rewrite lift_rec_null. 
eapply2 unequal_closed_normal_forms. 
simpl. max_out. 
rewrite H1; rewrite H2. 
split_all. 
discriminate. 
eval_lamSF. eval_lamSF.  eval_lamSF.  eval_lamSF. 
repeat (rewrite (subst_rec_closed has_combinator);  [| split_all]). 
unfold subst_rec; fold subst_rec. insert_Ref_out. 
rewrite subst_rec_lift_rec; try omega. rewrite lift_rec_null. 
match goal with 
| |- multi_step lamSF_red1 (App (App _ ?M)?N) _ => 
apply transitive_red with (App (App (App (App has_combinator i_op) (Abs M1)) M) N)
end. 
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red.
unfold has_combinator. 
fixtac. fold has_combinator. unfold has_combinator_fn. 
eval_lamSF. 
repeat (rewrite (subst_rec_closed equal_comb);  [| split_all]). 
unfold subst_rec; fold subst_rec. insert_Ref_out.
rewrite subst_rec_lift_rec; [|split_all|split_all]. 
rewrite lift_rec_closed.
2: split_all; omega. 
unfold subst_rec; fold subst_rec. insert_Ref_out. 
match goal with 
| |- multi_step lamSF_red1 (App (App _ ?M)?N) _ => 
apply transitive_red with (App (App (App k_op i_op) M)N) 
end. 
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red. 
rewrite lift_rec_null. 
eapply2 unequal_closed_normal_forms. 
simpl. max_out. 
discriminate. 
eval_lamSF. eval_lamSF.  eval_lamSF.  eval_lamSF. 
repeat (rewrite (subst_rec_closed has_combinator);  [| split_all]). 
unfold subst_rec; fold subst_rec. insert_Ref_out. 
match goal with 
| |- multi_step lamSF_red1 (App (App _ ?M)?N) _ => 
apply transitive_red with (App (App (App k_op i_op) M) N)
end. 
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red.
eapply2 has_combinator_rank.
simpl. omega. 
simpl. omega. 
eval_lamSF. eval_lamSF. auto. 
(* 2 : Abs -> star *)
match goal with 
| |- multi_step lamSF_red1 (App (App _ ?M)?N) _ => 
apply transitive_red with (App (App (App k_op i_op) M) N)
end. 
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red.
unfold has_combinator. fold lamSF_red. 
fixtac. fold has_combinator. unfold has_combinator_fn. 
eval_lamSF. 
repeat (rewrite (subst_rec_closed equal_comb);  [| split_all]). 
unfold subst_rec; fold subst_rec. insert_Ref_out.
rewrite subst_rec_lift_rec; [|split_all|split_all].
unfold subst_rec; fold subst_rec.  insert_Ref_out. 
rewrite lift_rec_null. 
match goal with 
| |- multi_step lamSF_red1 (App (App _ ?M)?N) _ => 
apply transitive_red with (App (App (App k_op i_op) M)N) 
end. 
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red. 
eapply2 unequal_closed_normal_forms. 
simpl. max_out. 
discriminate. 
eval_lamSF. eval_lamSF.
apply succ_red with (App (App  (Abs
           (Abs
              (App
                 (App
                    (App
                       (App
                          (subst_rec (lift_rec has_combinator 0 3) (Abs M1) 2)
                          (App (App (Op Sop) (App (Op Fop) (Op Fop)))
                             (App (Op Fop) (Op Fop)))) 
                       (Ref 1)) (App (Op Fop) (Op Fop)))
                 (App
                    (App (subst_rec (lift_rec has_combinator 0 3) (Abs M1) 2)
                       (App (App (Op Sop) (App (Op Fop) (Op Fop)))
                          (App (Op Fop) (Op Fop)))) 
                    (Ref 0))))) (left_component (Abs M1))) (right_component (Abs M1))).
eapply2 f_compound_lamSF_red.
assert((exists o, M1 = Op o) \/ compound M1). eapply2 not_active_factorable. 
simpl in H. inversion H; split_all. 
inversion H1; subst; split_all. 
subst. eapply2 abs_op_compound. 
eval_lamSF. 
repeat (rewrite (subst_rec_closed has_combinator);  [| split_all]). 
unfold subst_rec; fold subst_rec. insert_Ref_out.
unfold left_component, right_component. 
rewrite subst_rec_lift_rec; try omega. 
rewrite lift_rec_null. 
rewrite lift_rec_null. 
unfold_op. 
match goal with 
| |- multi_step lamSF_red1 (App (App _ ?M)?N) _ => 
apply transitive_red with (App (App (App k_op i_op) M)N) 
end. 
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red.
eapply2 has_combinator_rank. 
simpl. omega. 
simpl. omega. 
eval_lamSF; eval_lamSF. 
eapply2 IHp.
simpl in *; omega. 
max_out. 
eval_lamSF; eval_lamSF.
(* now M2 *) 
unfold has_combinator. fold lamSF_red. 
fixtac. fold has_combinator. unfold has_combinator_fn. 
eval_lamSF. 
repeat (rewrite (subst_rec_closed equal_comb);  [| split_all]). 
unfold subst_rec; fold subst_rec. insert_Ref_out.
rewrite subst_rec_lift_rec; [|split_all|split_all].
unfold subst_rec; fold subst_rec.  insert_Ref_out. 
rewrite lift_rec_null. 
match goal with 
| |- multi_step lamSF_red1 (App (App _ ?M)?N) _ => 
apply transitive_red with (App (App (App k_op i_op) M)N) 
end. 
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red. 
eapply2 unequal_closed_normal_forms. 
simpl. max_out. 
discriminate. 
eval_lamSF. eval_lamSF.
apply succ_red with (App (App  (Abs
           (Abs
              (App
                 (App
                    (App
                       (App
                          (subst_rec (lift_rec has_combinator 0 3) (Abs M2) 2)
                          (App (App (Op Sop) (App (Op Fop) (Op Fop)))
                             (App (Op Fop) (Op Fop)))) 
                       (Ref 1)) (App (Op Fop) (Op Fop)))
                 (App
                    (App (subst_rec (lift_rec has_combinator 0 3) (Abs M2) 2)
                       (App (App (Op Sop) (App (Op Fop) (Op Fop)))
                          (App (Op Fop) (Op Fop)))) 
                    (Ref 0))))) (left_component (Abs M2))) (right_component (Abs M2))).
eapply2 f_compound_lamSF_red.
assert((exists o, M2 = Op o) \/ compound M2). eapply2 not_active_factorable.
max_out. 
assert(status M2 <= maxvar M2) by eapply2 status_lt_maxvar. 
omega.  
inversion H1; subst; split_all. 
subst. eapply2 abs_op_compound. 
eval_lamSF. 
repeat (rewrite (subst_rec_closed has_combinator);  [| split_all]). 
unfold subst_rec; fold subst_rec. insert_Ref_out.
unfold left_component, right_component. 
rewrite subst_rec_lift_rec; try omega. 
rewrite lift_rec_null. 
rewrite lift_rec_null. 
unfold_op. 
match goal with 
| |- multi_step lamSF_red1 (App (App _ ?M)?N) _ => 
apply transitive_red with (App (App (App k_op i_op) M)N) 
end. 
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red.
eapply2 has_combinator_rank. 
simpl. omega. 
simpl. omega. 
eval_lamSF; eval_lamSF. 
eapply2 IHp.
simpl in *; omega. 
max_out. 
Qed. 


