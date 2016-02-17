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
(*                    Analysis.v                                      *)
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
Require Import Eta.
Require Import Equal.
Require Import Combinators.
Require Import Binding.


(* unstar *) 


(* 
Fixpoint star M := 
match M with 
| Ref 0 => i_op 
| Ref (S n) => App k_op (Ref n)
| Op o => App k_op (Op o)
| Abs M1 =>  Abs (star M1)
| App M1 M2 => App (App s_op (Abs M1)) (Abs M2)
end
.

unstar = 
| S M N => abs_S M N 
| K M => abs_K M 
| M as Abs _ => Abs (unstar (M (Ref 0)))
| O => O


*) 

Definition unstar_fn := 
Abs (Abs (App (App (App f_op (Ref 0)) (Ref 0)) (Abs (Abs 
(App (App (App (App equal_comb abs_left) (Ref 1)) (Abs (App (Ref 4) (App (Ref 3) (Ref 0)))))
(App (App (App (App equal_comb k_op) (Ref 1)) (App abs_K (Ref 0)))
(App (App (App f_op (Ref 1)) (Ref 2)) (Abs (Abs 
(App (App abs_S (Ref 0)) (Ref 2))
)))))))))
.

Definition unstar := App fixpoint unstar_fn. 

Theorem unstar_star : forall M, normal M -> lamSF_red (App unstar (star M)) (Abs M). 
Proof. 
induction M; split_all. 
(* 4 *) 
unfold unstar. fixtac. fold unstar. unfold unstar_fn. 
case n; split_all. 
(* 5 *) 
eval_lamSF. unfold subst_rec; fold subst_rec. insert_Ref_out. 
eval_lamSF. eval_lamSF. 
repeat (rewrite (subst_rec_closed equal_comb);  [| split_all]). 
repeat (rewrite (subst_rec_closed unstar);  [| split_all]). 
unfold subst_rec; fold subst_rec. insert_Ref_out.
repeat (rewrite (subst_rec_closed abs_K);  [| split_all]). 
match goal with 
| |- multi_step lamSF_red1 (App (App _ ?M)?N) _ => 
apply transitive_red with (App (App (App k_op i_op) M)N) 
end. 
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red. 
eapply2 unequal_programs; split_all. 
eval_lamSF.  eval_lamSF.
match goal with 
| |- multi_step lamSF_red1 (App (App _ ?M)?N) _ => 
apply transitive_red with (App (App (App k_op i_op) M)N) 
end. 
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red. 
eapply2 unequal_programs; split_all. 
eval_lamSF.  eval_lamSF. eval_lamSF.  eval_lamSF.
repeat (rewrite (subst_rec_closed abs_S);  [| split_all]). 
unfold abs_S. 
eval_lamSF. 
unfold subst_rec; fold subst_rec. insert_Ref_out.
eapply2 preserves_abs_lamSF_red. 
(* 4 *) 
eval_lamSF. 
unfold subst_rec; fold subst_rec. insert_Ref_out.
eval_lamSF. eval_lamSF. 
repeat (rewrite (subst_rec_closed equal_comb);  [| split_all]). 
unfold subst_rec; fold subst_rec. insert_Ref_out.
match goal with 
| |- multi_step lamSF_red1 (App (App _ ?M)?N) _ => 
apply transitive_red with (App (App (App k_op i_op) M)N) 
end. 
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red. 
eapply2 unequal_programs; split_all. 
eval_lamSF.  eval_lamSF.
match goal with 
| |- multi_step lamSF_red1 (App (App _ ?M)?N) _ => 
apply transitive_red with (App (App k_op M)N) 
end. 
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red. 
eapply2 equal_programs; split_all. 
eval_lamSF.  
repeat (rewrite (subst_rec_closed abs_K);  [| split_all]). 
unfold abs_K. 
eval_lamSF. 
relocate_lt. 
simpl. auto. 
(* 3 *) 
unfold unstar. fixtac. fold unstar. unfold unstar_fn. 
eval_lamSF. unfold subst_rec; fold subst_rec. insert_Ref_out. 
eval_lamSF. eval_lamSF. 
repeat (rewrite (subst_rec_closed equal_comb);  [| split_all]). 
repeat (rewrite (subst_rec_closed unstar);  [| split_all]). 
unfold subst_rec; fold subst_rec. insert_Ref_out.
match goal with 
| |- multi_step lamSF_red1 (App (App _ ?M)?N) _ => 
apply transitive_red with (App (App (App k_op i_op) M)N) 
end. 
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red. 
eapply2 unequal_programs; split_all. 
eval_lamSF.  eval_lamSF.
match goal with 
| |- multi_step lamSF_red1 (App (App _ ?M)?N) _ => 
apply transitive_red with (App (App k_op M)N) 
end. 
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red. 
eapply2 equal_programs; split_all. 
eval_lamSF.  
repeat (rewrite (subst_rec_closed abs_K);  [| split_all]). 
unfold abs_K. eval_lamSF. auto. 
(* 2 *) 
unfold unstar. fixtac. fold unstar. unfold unstar_fn. 
eval_lamSF. unfold subst_rec; fold subst_rec. insert_Ref_out. 
match goal with 
| |- multi_step lamSF_red1 (App (App (App (Op Fop) ?M1) _)?N) _ => 
apply succ_red with (App (App N (left_component M1)) (right_component M1))
end.
eapply2 f_compound_lamSF_red. 
rewrite lift_rec_preserves_star. rewrite lift_rec_null. 
eapply2 abs_compound_compound. 
eapply2 star_compound. 
eval_lamSF. 
repeat (rewrite (subst_rec_closed equal_comb);  [| split_all]).
unfold left_component; fold left_component. 
 rewrite lift_rec_closed;[| split_all]. 
 rewrite subst_rec_closed;[| split_all]. 
match goal with 
| |- multi_step lamSF_red1 (App (App _ ?M)?N) _ => 
apply transitive_red with (App (App k_op M)N) 
end. 
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red. 
unfold_op. 
eapply2 equal_programs; split_all. 
eval_lamSF.
eapply2 preserves_abs_lamSF_red. 
rewrite subst_rec_lift_rec; try omega. 
rewrite subst_rec_lift_rec; try omega. 
rewrite subst_rec_lift_rec; try omega. 
rewrite lift_rec_closed. 2: split_all. 
rewrite subst_rec_lift_rec; try omega. 
rewrite subst_rec_lift_rec; try omega. 
apply transitive_red with (App unstar (star M)).
eapply2 preserves_app_lamSF_red. 
eval_lamSF. 
rewrite subst_rec_lift_rec2.
auto. 
inversion H; eapply2 IHM. 
(* 1 *) 
unfold unstar. fixtac. fold unstar. unfold unstar_fn. 
eval_lamSF. unfold subst_rec; fold subst_rec. insert_Ref_out. 
eval_lamSF. eval_lamSF. 
repeat (rewrite (subst_rec_closed equal_comb);  [| split_all]).
unfold subst_rec; fold subst_rec. insert_Ref_out. 
match goal with 
| |- multi_step lamSF_red1 (App (App _ ?M)?N) _ => 
apply transitive_red with (App (App (App k_op i_op) M)N) 
end. 
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red. 
match goal with
| |- lamSF_red (App (App _ ?M) ?N) _ => 
apply transitive_red with 
(App (App (App (App equal_comb (left_component M)) (left_component N))
 (App (App equal_comb (right_component M)) (right_component N)))
(App k_op i_op))
end.
eapply2 equal_compounds. 
simpl. 
match goal with
| |- multi_step lamSF_red1 (App (App _ ?M) ?N) _ => 
apply transitive_red with 
(App (App (App k_op i_op) M) N)
end.
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red. 
eapply2 unequal_programs; split_all. 
eval_lamSF. eval_lamSF. auto. 
eval_lamSF. eval_lamSF. 
match goal with
| |- multi_step lamSF_red1 (App (App _ ?M) ?N) _ => 
apply transitive_red with 
(App (App (App k_op i_op) M) N)
end.
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red. 
match goal with
| |- lamSF_red (App (App _ ?M) ?N) _ => 
apply transitive_red with 
(App (App (App (App equal_comb (left_component M)) (left_component N))
 (App (App equal_comb (right_component M)) (right_component N)))
(App k_op i_op))
end.
eapply2 equal_compounds. 
simpl. 
match goal with
| |- multi_step lamSF_red1 (App (App _ ?M) ?N) _ => 
apply transitive_red with 
(App (App (App k_op i_op) M) N)
end.
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red. 
eapply2 unequal_programs; split_all. 
eval_lamSF. eval_lamSF. auto. 
eval_lamSF. eval_lamSF. 
eval_lamSF. eval_lamSF. 
repeat (rewrite (subst_rec_closed equal_comb);  [| split_all]).
unfold abs_S; unfold subst_rec; fold subst_rec. insert_Ref_out. 
eval_lamSF. 
unfold subst_rec; fold subst_rec. insert_Ref_out. 
eapply2 preserves_abs_lamSF_red. 
unfold subst_rec; fold subst_rec. insert_Ref_out. 
unfold subst_rec; fold subst_rec. insert_Ref_out. 
unfold subst_rec; fold subst_rec. insert_Ref_out. 
unfold subst_rec; fold subst_rec. insert_Ref_out. 
unfold subst_rec; fold subst_rec. insert_Ref_out. 
rewrite subst_rec_lift_rec; try omega. 
rewrite subst_rec_lift_rec; try omega. 
rewrite lift_rec_lift_rec; try omega. 
rewrite lift_rec_null. 
simpl. 
rewrite subst_rec_lift_rec; try omega. 
rewrite subst_rec_lift_rec; try omega. 
rewrite lift_rec_lift_rec; try omega. 
simpl. 
eapply2 preserves_app_lamSF_red. 
eval_lamSF. 
rewrite subst_rec_lift_rec2. auto. 
eval_lamSF. 
rewrite subst_rec_lift_rec2. auto. 

Qed. 


Definition wait M N := App (App s_op (App (App s_op (App k_op M)) (App k_op N))) i_op .

Lemma rank_wait : forall M N, rank (wait M N) = 23 + rank M + rank N. 
Proof. unfold_op; unfold rank; fold rank. split_all. omega. Qed. 

Definition tag T M :=  App (App s_op (App k_op M)) (App (App s_op k_op) T). 

(* 
Definition abs_left := App (App s_op k_op) f_op
*) 
Definition abs_tag := tag f_op.
Definition com_tag := tag s_op.
Definition app_tag M N := tag k_op (wait M N).

Ltac unfold_op ::= unfold abs_tag, abs_left, com_tag, app_tag, tag, wait, i_op, id, k_op, f_op, s_op.


Lemma tag_ext : forall T M, beta_eta_eq (tag T M) M. 
Proof. split_all; unfold tag; unfold_op. 
assert(beta_eta_eq (App (App (Op Sop) (App (App (Op Fop) (Op Fop)) M))
        (App (App (Op Sop) (App (Op Fop) (Op Fop))) T)) (Abs (App (lift_rec (App (App (Op Sop) (App (App (Op Fop) (Op Fop)) M))
        (App (App (Op Sop) (App (Op Fop) (Op Fop))) T)) 0 1) (Ref 0)))) . 
eapply2 symm_etared. 
simpl in *. 
assert(beta_eta_eq  (Abs
           (App
              (App
                 (App (Op Sop) (App (App (Op Fop) (Op Fop)) (lift_rec M 0 1)))
                 (App (App (Op Sop) (App (Op Fop) (Op Fop))) (lift_rec T 0 1)))
              (Ref 0))) 
(Abs (App (lift_rec M 0 1) (Ref 0)))). 
eapply2 abs_etared.
assert(beta_eta_eq  (App
        (App (App (Op Sop) (App (App (Op Fop) (Op Fop)) (lift_rec M 0 1)))
           (App (App (Op Sop) (App (Op Fop) (Op Fop))) (lift_rec T 0 1)))
        (Ref 0)) 
(App (App (App (App (Op Fop) (Op Fop)) (lift_rec M 0 1)) (Ref 0))
(App (App (App (Op Sop) (App (Op Fop) (Op Fop))) (lift_rec T 0 1))
        (Ref 0)))). auto. 
assert(beta_eta_eq
(App (App (App (App (Op Fop) (Op Fop)) (lift_rec M 0 1)) (Ref 0))
(App (App (App (Op Sop) (App (Op Fop) (Op Fop))) (lift_rec T 0 1))
        (Ref 0)))
 (App (lift_rec M 0 1) (Ref 0))).
eapply2 app_etared. 
eauto. 
eauto. 
Qed. 


(* to_combinator_int *) 

(* 
to_combinator_int := 
| O => O
| Abs M => abs_tag (to_combinator_int (if binds (star M) then (star M) else (KM)))
| M N => if is_combinator (M N) 
         then com_tag (M N) 
         else app_tag (to_combinator_int M) (to_combinator_int N))

*) 

Definition to_comb_int_fn := 
Abs (Abs  (App (App (App (Op Fop) (Ref 0)) (Ref 0)) (Abs (Abs 
(App (App (App (App equal_comb abs_left) (Ref 1)) (abs_tag (App (Ref 3)
(App (App (App binds (Ref 0)) (Ref 0)) (App k_op (App (Ref 2) f_op))))))
(App (App (App is_comb (Ref 2)) (com_tag (Ref 2))) (app_tag (App (Ref 3) (Ref 1)) (App (Ref 3) (Ref 0))))))))).


Definition to_comb_int := App fixpoint to_comb_int_fn. 

Lemma to_comb_int_op : forall o, lamSF_red (App to_comb_int (Op o)) (Op o). 
Proof. 
split_all; unfold to_comb_int. fixtac. fold to_comb_int.  unfold to_comb_int_fn; unfold_op; repeat eval_lamSF. auto. 
Qed. 


Lemma to_comb_int_abs_0: forall M, normal M -> maxvar M = 0 -> 
lamSF_red (App to_comb_int (Abs M)) (abs_tag  (App to_comb_int (App k_op M))).
Proof. 
split_all; unfold to_comb_int. fixtac. unfold to_comb_int_fn at 1. fold to_comb_int. 
eval_lamSF. unfold subst_rec; fold subst_rec. insert_Ref_out. rewrite lift_rec_null. 
match goal with 
| |- multi_step lamSF_red1 (App (App (App (Op Fop) ?M) _) ?N) _ => 
  apply succ_red with (App (App N (left_component M)) (right_component M));
[eapply2 f_compound_lamSF_red|]
end.  
assert((exists o, Abs M = Op o) \/ (compound (Abs M))).
eapply2 normal_closed_is_factorable. simpl in *; omega. 
inversion H1; split_all; subst;split_all. 
eval_lamSF. 
repeat (rewrite (subst_rec_closed equal_comb); [| split_all]). 
repeat (rewrite (subst_rec_lift_rec); [| split_all | split_all]). 
repeat (rewrite lift_rec_null).
insert_Ref_out. 
repeat (rewrite lift_rec_null).
unfold left_component, right_component. 
match goal with
| |- multi_step lamSF_red1 (App (App _ ?M) ?N) _ => 
apply transitive_red with 
(App (App k_op M) N)
end.
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red. 
unfold_op. 
eapply2 equal_closed_normal_forms.
eval_lamSF.
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red. 
repeat (rewrite (subst_rec_closed binds); [| split_all]). 
match goal with
| |- lamSF_red (App (App _ ?M) ?N) _ => 
apply transitive_red with 
(App (App (App k_op i_op) M) N)
end.
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red. 
eapply2 binds_star_0.
eval_lamSF. eval_lamSF. 
eapply2 preserves_app_lamSF_red. 
eval_lamSF. 
rewrite subst_rec_closed; split_all. 
omega. 
Qed. 


Lemma to_comb_int_abs_1: forall M, normal M -> maxvar M =1 -> 
lamSF_red (App to_comb_int (Abs M)) (abs_tag (App to_comb_int (star M)))
.
Proof. 
split_all; unfold to_comb_int. fixtac. unfold to_comb_int_fn at 1. fold to_comb_int. 
eval_lamSF. unfold subst_rec; fold subst_rec. insert_Ref_out. rewrite lift_rec_null. 
match goal with 
| |- multi_step lamSF_red1 (App (App (App (Op Fop) ?M) _) ?N) _ => 
  apply succ_red with (App (App N (left_component M)) (right_component M));
[eapply2 f_compound_lamSF_red|]
end.  
eval_lamSF. 
repeat (rewrite (subst_rec_closed equal_comb); [| split_all]). 
repeat (rewrite (subst_rec_lift_rec); [| split_all | split_all]). 
repeat (rewrite lift_rec_null).
insert_Ref_out. 
assert((exists o, Abs M = Op o) \/ (compound (Abs M))).
eapply2 normal_closed_is_factorable. simpl in *. omega. 
inversion H1; split_all; subst;split_all. 
eval_lamSF. 
repeat (rewrite (subst_rec_closed equal_comb); [| split_all]). 
repeat (rewrite (subst_rec_lift_rec); [| split_all | split_all]). 
repeat (rewrite lift_rec_null).
unfold left_component, right_component. 
match goal with
| |- multi_step lamSF_red1 (App (App _ ?M) ?N) _ => 
apply transitive_red with 
(App (App k_op M) N)
end.
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red. 
unfold_op. 
eapply2 equal_closed_normal_forms. 
eval_lamSF.
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red. 
repeat (rewrite (subst_rec_closed binds); [| split_all]). 
apply transitive_red with (App (App k_op  (star M))
       (App (App (Op Fop) (Op Fop)) (App (Abs M) (Op Fop)))).
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red. 
eapply2 binds_star_1. 
eval_lamSF. 
auto.
Qed. 


Lemma to_comb_int_compound_combinator: forall M, compound M -> combinator M -> normal M ->
lamSF_red (App to_comb_int M) (com_tag (App (left_component M) (right_component M)))
.
Proof. 
split_all; unfold to_comb_int. fixtac. unfold to_comb_int_fn at 1. fold to_comb_int. 
eval_lamSF. unfold subst_rec; fold subst_rec. insert_Ref_out. rewrite lift_rec_null. 
match goal with 
| |- multi_step lamSF_red1 (App (App (App (Op Fop) ?M) _) ?N) _ => 
  apply succ_red with (App (App N (left_component M)) (right_component M));
[eapply2 f_compound_lamSF_red|]
end.  
eval_lamSF. 
repeat (rewrite (subst_rec_closed equal_comb); [| split_all]). 
repeat (rewrite (subst_rec_lift_rec); [| split_all | split_all]). 
repeat (rewrite lift_rec_null).
match goal with
| |- multi_step lamSF_red1 (App (App _ ?M) ?N) _ => 
apply transitive_red with 
(App (App (App k_op i_op) M) N)
end.
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red.
eapply2 unequal_closed_normal_forms.  
gen_inv H0 H; unfold_op; auto. subst. inversion H1; auto. 
assert(maxvar M = 0) by eapply2 maxvar_combinator. 
gen_inv H2 H0. max_out. 
gen_inv H H0; try discriminate. 
inversion H2. 
inversion H4; discriminate. 
eval_lamSF; eval_lamSF. 
repeat(rewrite (subst_rec_closed is_comb); try (split_all; omega)). 
match goal with
| |- multi_step lamSF_red1 (App (App _ ?M1) ?N) _ => 
apply transitive_red with 
(App (App k_op M1) N)
end.
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red.
eapply2 is_comb_true.
eval_lamSF. 
eapply2 preserves_app_lamSF_red. 
gen_case H H0; split_all. 
inversion H. 
Qed. 


Lemma to_comb_int_compound_not_combinator: forall M, compound M -> left_component M <>abs_left -> normal M -> maxvar M = 0 -> (combinator M -> False) -> 
lamSF_red (App to_comb_int M) (app_tag (App to_comb_int (left_component M)) (App to_comb_int  (right_component M)))
.
Proof. 
split_all; unfold to_comb_int. fixtac. unfold to_comb_int_fn at 1. fold to_comb_int. 
eval_lamSF. unfold subst_rec; fold subst_rec. insert_Ref_out. rewrite lift_rec_null. 
match goal with 
| |- multi_step lamSF_red1 (App (App (App (Op Fop) ?M) _) ?N) _ => 
  apply succ_red with (App (App N (left_component M)) (right_component M));
[eapply2 f_compound_lamSF_red|]
end.  
eval_lamSF. 
repeat (rewrite (subst_rec_closed equal_comb); [| split_all]). 
repeat (rewrite (subst_rec_lift_rec); [| split_all | split_all]). 
repeat (rewrite lift_rec_null).
match goal with
| |- multi_step lamSF_red1 (App (App _ ?M) ?N) _ => 
apply transitive_red with 
(App (App (App k_op i_op) M) N)
end.
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red. 
unfold abs_tag in *.
gen2_inv H0 H1 H.  
eapply2 unequal_closed_normal_forms.
match goal with
| |- lamSF_red (App (App _ ?M) ?N) _ => 
apply transitive_red with 
(App (App (App (App equal_comb (left_component M)) (left_component N))
 (App (App equal_comb (right_component M)) (right_component N)))
(App k_op i_op))
end.
eapply2 equal_compounds. 
simpl. 
match goal with
| |- multi_step lamSF_red1 (App (App _ ?M) ?N) _ => 
apply transitive_red with 
(App (App (App k_op i_op) M) N)
end.
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red. 
eapply2 unequal_closed_normal_forms. 
discriminate. 
eval_lamSF. eval_lamSF. auto. 
eval_lamSF. eval_lamSF. 
repeat (rewrite (subst_rec_closed is_comb); [| split_all]). 
match goal with
| |- multi_step lamSF_red1 (App (App _ ?M) ?N) _ => 
apply transitive_red with 
(App (App (App k_op i_op) M) N)
end.
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red. 
eapply2 is_comb_false. 
eval_lamSF; eval_lamSF. 
eapply2 preserves_app_lamSF_red. 
Qed. 



(* unwait

Definition wait M N :=  S (S(KM)(KN)) I

unwait := 

| wait M N  => S M N 


*) 


Definition unwait  := Abs (
App (App (App f_op (Ref 0)) (Ref 0)) (Abs (Abs (   (*Ref 1 = S (S(KM)(KN)), Ref 0 = I *) 
App (App (App f_op (Ref 1)) f_op) (Abs (Abs (   (* Ref 1 = S, Ref 0 =  (S(KM)(KN)) *) 
App (App (App f_op (Ref 0)) f_op) (Abs (Abs (  (* Ref 1 = S(KM), Ref 0 = KN *) 
App (App (App f_op (Ref 1)) f_op) (Abs (Abs (  (* Ref 1 = S, Ref 0 = KM *) 
App (App s_op 
(App (App (App f_op (Ref 0)) f_op) (Abs (Abs (Ref 0))))) (* Ref 0 = KM *)
(App (App (App f_op (Ref 2)) f_op) (Abs (Abs (Ref 0)))) (* Ref 2 = KN *)
)))))))))))))
.

Lemma unwait_op : forall o, lamSF_red (App unwait (Op o)) (Op o). 
Proof. split_all. unfold unwait. unfold_op. eval_lamSF. eval_lamSF. auto. Qed.

Lemma unwait_wait : 
 forall M N, lamSF_red (App unwait (wait M N)) (App (App s_op M) N). 
Proof. 
split_all. unfold unwait. unfold_op. 
eval_lamSF. eval_lamSF. eval_lamSF. 
unfold subst_rec; fold subst_rec. insert_Ref_out. 
eval_lamSF. eval_lamSF. 
unfold subst_rec; fold subst_rec. insert_Ref_out. 
eval_lamSF. eval_lamSF. 
 unfold subst_rec; fold subst_rec. insert_Ref_out. 
eval_lamSF. eval_lamSF. 
 unfold subst_rec; fold subst_rec. insert_Ref_out. 
eval_lamSF.
 unfold subst_rec; fold subst_rec. insert_Ref_out.
rewrite subst_rec_lift_rec; split_all.  
rewrite subst_rec_lift_rec; split_all.  
rewrite subst_rec_lift_rec; split_all.  
rewrite subst_rec_lift_rec; split_all.  
rewrite subst_rec_lift_rec; split_all.  
rewrite lift_rec_null. 
rewrite lift_rec_null. 
eapply2 preserves_app_lamSF_red.  
eapply2 preserves_app_lamSF_red.  
eval_lamSF. eval_lamSF. 
unfold subst_rec; fold subst_rec. insert_Ref_out. 
rewrite lift_rec_null. auto. 
eval_lamSF. eval_lamSF.
unfold subst_rec; fold subst_rec. insert_Ref_out. 
rewrite lift_rec_null. auto. 
Qed. 



(* untag

Definition tag T M :=  App (App s_op (App k_op M)) (App (App s_op  k_op) T)).

| tag T M  => S T M


*) 

Definition untag  := Abs (
App (App (App f_op (Ref 0)) (Ref 0)) (Abs (Abs (App (App s_op    (* Ref 1 = S(KM), Ref 0 = SKT *) 
(App (App (App f_op (Ref 0)) f_op) (Abs (Abs (Ref 0)))))         (* Ref 1 = SK, Ref 0 = T *)  
(App (App (App f_op (Ref 1)) f_op) (Abs (Abs (                   (* Ref 1 = S, Ref 0 = KM *) 
App (App (App f_op (Ref 0)) f_op) (Abs (Abs (Ref 0)))            (* Ref 1 = K, Ref 0 = M *) 
))))))))
.

Lemma untag_op : forall o, lamSF_red (App untag (Op o)) (Op o). 
Proof. split_all. unfold untag. unfold_op. eval_lamSF. eval_lamSF. auto. Qed.

Lemma untag_tag : 
 forall T M, lamSF_red (App untag (tag T M)) (App (App s_op T) M).
Proof. 
split_all. unfold untag. unfold_op. 
eval_lamSF. eval_lamSF. eval_lamSF. 
unfold subst_rec; fold subst_rec. insert_Ref_out. 
eval_lamSF.
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red. 
eval_lamSF. eval_lamSF. 
unfold subst_rec; fold subst_rec. insert_Ref_out. rewrite lift_rec_null.
auto. 
eval_lamSF. eval_lamSF. 
 unfold subst_rec; fold subst_rec. insert_Ref_out. 
eval_lamSF. eval_lamSF. 
 unfold subst_rec; fold subst_rec. insert_Ref_out. 
rewrite subst_rec_lift_rec; split_all.  
rewrite lift_rec_null. 
rewrite lift_rec_null. 
auto. 
Qed. 


(* 
to_comb_int := 
| O => O
| Abs M => abs_tag (to_comb_int (if binds (star M) then (star M) else (KM)))
| M N => if is_combinator (M N) 
         then com_tag (M N) 
         else app_tag (to_comb_int M) (to_comb_int N))

abstract:= 
| O => O 
| abs_tag _ M => unstar (abstract M) 
| com_tag M => M
| app_tag (wait M N) => (abstract M) (abstract N)
*) 


Definition abstract_fn := 

Abs (Abs 
(App (App (App (Op Fop) (App untag (Ref 0))) (Ref 0)) (Abs (Abs 
(App (App (App (Op Fop) (Ref 1)) (Ref 1)) (Abs (Abs 
(App (App (App (App equal_comb f_op) (Ref 0)) 
          (App unstar (App (Ref 5) (Ref 2))))
     (App (App (App (App equal_comb s_op) (Ref 0)) (Ref 2)) 
          (App (App (App f_op (App unwait (Ref 2))) f_op) (Abs (Abs 
    (App (App (App f_op (Ref 1)) f_op) (Abs (Abs (App (App (Ref 9) (Ref 0)) (App (Ref 9) (Ref 2))))))
))))))))))))
.


Definition abstract := App fixpoint abstract_fn. 


Lemma abstract_op : forall o, lamSF_red (App abstract (Op o)) (Op o). 
Proof. 
split_all; unfold abstract. fixtac. fold abstract. 
unfold abstract_fn. 
eval_lamSF. 
repeat (rewrite (subst_rec_closed unwait); [|split_all]). 
unfold subst_rec; fold subst_rec; insert_Ref_out. 
match goal with 
| |- multi_step lamSF_red1 (App (App _ ?M)?N) _ => 
apply transitive_red with (App (App (App f_op (Op o)) M) N)
end. 
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red.
repeat (rewrite (subst_rec_closed untag); [|split_all]). 
eapply2 untag_op. 
eval_lamSF.
auto. 
omega. 
Qed. 


Lemma abstract_abs_tag: 
forall M, lamSF_red (App abstract (abs_tag M)) (App unstar (App abstract M)). 
Proof. 
split_all; unfold abstract. fixtac.  fold abstract. unfold abstract_fn. 
eval_lamSF. unfold subst_rec ; fold subst_rec; insert_Ref_out. 
rewrite lift_rec_null. 
repeat (rewrite (subst_rec_closed untag); [| split_all]). 
match goal with 
| |- _ _ (App (App (App _ (App untag ?M1))_)_) _ => 
replace M1 with (abs_tag M) by split_all
end. 
match goal with 
| |- _ _ (App (App _ ?M1)?N1) _ => 
apply transitive_red with (App (App (App f_op (App (App s_op f_op) M)) M1) N1)
end. 
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red. 
eapply2 untag_tag. 
eval_lamSF. eval_lamSF.
 unfold subst_rec ; fold subst_rec; insert_Ref_out. 
eval_lamSF. eval_lamSF.
repeat (rewrite (subst_rec_closed equal_comb); [|split_all]). 
 unfold subst_rec ; fold subst_rec; insert_Ref_out.
rewrite subst_rec_lift_rec; [|split_all|split_all]. 
match goal with 
| |- _ _ (App (App _ ?M)?N) _ => 
apply transitive_red with (App (App k_op M) N)
end. 
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red. 
eapply2 equal_closed_normal_forms; discriminate. 
eval_lamSF. 
repeat (rewrite (subst_rec_closed unstar); [| split_all]). 
repeat (rewrite (subst_rec_lift_rec abstract); try omega). 
repeat (rewrite (subst_rec_lift_rec M); try omega). 
repeat (rewrite lift_rec_null). 
auto. 
Qed. 

Lemma abstract_com_tag: forall M, lamSF_red (App abstract (com_tag M)) M .
Proof. 
split_all; unfold abstract. fixtac.  fold abstract. unfold abstract_fn. 
eval_lamSF. unfold subst_rec ; fold subst_rec; insert_Ref_out. 
rewrite lift_rec_null. 
repeat (rewrite (subst_rec_closed untag); [|split_all]). 
match goal with 
| |- _ _ (App (App (App _ (App untag ?M1))_)_) _ => 
replace M1 with (com_tag M) by split_all
end. 
match goal with 
| |- _ _ (App (App _ ?M1)?N1) _ => 
apply transitive_red with (App (App (App f_op (App (App s_op s_op) M)) M1) N1)
end. 
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red. 
eapply2 untag_tag.
eval_lamSF. eval_lamSF.
 unfold subst_rec ; fold subst_rec; insert_Ref_out. 
eval_lamSF. eval_lamSF.
repeat (rewrite (subst_rec_closed equal_comb); [|split_all]). 
 unfold subst_rec ; fold subst_rec; insert_Ref_out. 
repeat (rewrite (subst_rec_closed unstar); [|split_all]). 
repeat (rewrite (subst_rec_lift_rec abstract); try omega).
match goal with 
| |- _ _ (App (App _ ?M)?N) _ => 
apply transitive_red with (App (App (App k_op i_op) M) N)
end. 
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red. 
eapply2 unequal_closed_normal_forms; discriminate. 
eval_lamSF. eval_lamSF. 
match goal with 
| |- _ _ (App (App _ ?M)?N) _ => 
apply transitive_red with (App (App k_op M) N)
end. 
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red. 
eapply2 equal_closed_normal_forms; discriminate. 
eval_lamSF. 
rewrite subst_rec_lift_rec; [|split_all|split_all]; try omega. 
rewrite subst_rec_lift_rec; [|split_all|split_all]; try omega. 
rewrite lift_rec_null.
auto.
Qed. 


Lemma abstract_app_tag: 
forall M N, 
lamSF_red (App abstract (app_tag M N))  (App (App abstract M) (App abstract N)).
Proof. 
split_all; unfold abstract. fixtac.  fold abstract. unfold abstract_fn. 
eval_lamSF. 
repeat (rewrite (subst_rec_closed untag); [|split_all]). 
unfold subst_rec ; fold subst_rec; insert_Ref_out. 
rewrite lift_rec_null. rewrite lift_rec_null. 
match goal with 
| |- _ _ (App (App (App _ (App untag ?M1))_)_) _ => 
replace M1 with (app_tag M N) by split_all
end. 
match goal with 
| |- _ _ (App (App _ ?M1)?N1) _ => 
apply transitive_red with (App (App (App f_op (App (App s_op k_op) (wait M N))) M1) N1)
end. 
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red. 
eapply2 untag_tag. 
eval_lamSF. eval_lamSF.
 unfold subst_rec ; fold subst_rec; insert_Ref_out. 
eval_lamSF. eval_lamSF.
repeat (rewrite (subst_rec_closed equal_comb); [|split_all]). 
 unfold subst_rec ; fold subst_rec; insert_Ref_out. 
repeat (rewrite (subst_rec_closed unstar); [|split_all]). 
rewrite subst_rec_lift_rec; [|split_all|split_all]. 
match goal with 
| |- _ _ (App (App _ ?M)?N) _ => 
apply transitive_red with (App (App (App k_op i_op) M) N)
end. 
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red. 
eapply2 unequal_closed_normal_forms; discriminate. 
eval_lamSF. eval_lamSF. 
match goal with 
| |- _ _ (App (App _ ?M)?N) _ => 
apply transitive_red with (App (App (App k_op i_op) M) N)
end. 
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red. 
eapply2 unequal_closed_normal_forms; discriminate. 
eval_lamSF. eval_lamSF. 
repeat (rewrite (subst_rec_closed unwait); [|split_all]). 
rewrite subst_rec_lift_rec; [|split_all|split_all]. 
rewrite subst_rec_lift_rec; [|split_all|split_all]. 
rewrite subst_rec_lift_rec; [|split_all|split_all]. 
rewrite subst_rec_lift_rec; [|split_all|split_all]. 
rewrite lift_rec_null.
rewrite lift_rec_null.
match goal with 
| |- _ _ (App (App (App _ (App unwait ?M1))_)_) _ => 
replace M1 with (wait M N) by split_all
end. 
match goal with 
| |- _ _ (App (App _ ?M1)?N1) _ =>  
apply transitive_red with (App (App (App f_op (App (App s_op M) N)) M1) N1)
end. 
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red. 
eapply2 unwait_wait.
eval_lamSF. eval_lamSF.
 unfold subst_rec ; fold subst_rec; insert_Ref_out. 
eval_lamSF. eval_lamSF.
repeat (rewrite (subst_rec_lift_rec abstract); try omega). 
unfold subst_rec; fold subst_rec. 
insert_Ref_out. 
rewrite subst_rec_lift_rec; [|split_all|split_all]. 
rewrite subst_rec_lift_rec; [|split_all|split_all]. 
rewrite subst_rec_lift_rec; [|split_all|split_all]. 
repeat(rewrite lift_rec_null). 
auto.
Qed. 




Theorem to_comb_int_combinator:
forall M, normal M ->  maxvar M = 0 -> exists N, lamSF_red (App to_comb_int M) N /\ combinator N. 
Proof.
cut (forall p M, p >= rank M -> normal M ->  maxvar M = 0 -> exists N, lamSF_red (App to_comb_int M) N /\ combinator N). 
split_all. eapply2 H. 
induction p.
split_all. assert(rank M >0) by eapply2 rank_positive. noway. 
(* p > 0 *) 
intros M rnk nor; induction nor; split_all. 
(* 4 *) 
exist (Op o). 
eapply2 to_comb_int_op. 
(* 3 *)
assert(maxvar M = 0 \/ maxvar M = 1) by omega. 
inversion H0. 
(* 4 *) 
elim(IHp (App k_op M)); split_all. 
exist (abs_tag x).
apply transitive_red with (abs_tag (App to_comb_int (App k_op M))).  
eapply2 to_comb_int_abs_0. 
unfold_op. 
eapply2 preserves_app_lamSF_red. 
unfold_op; auto.
repeat (eapply2 comb_app). 
assert(rank M > 0) by eapply2 rank_positive. 
assert(rank(App k_op M) < rank (Abs M)); simpl in *;  omega; simpl in *; omega. 
unfold_op; auto. 
(* 3 *) 
elim(IHp (star M)); split_all. 
exist (abs_tag x).
apply transitive_red with (abs_tag (App to_comb_int (star M))).  
eapply2 to_comb_int_abs_1. 
unfold_op. 
eapply2 preserves_app_lamSF_red. 
unfold_op; auto.
repeat (eapply2 comb_app). 
assert(rank M > 0) by eapply2 rank_positive. 
assert(rank(star M) < rank (Abs M)). eapply2 rank_star. omega.
eapply2 normal_star. 
rewrite maxvar_star. omega. 
(* 2 *) 
assert(status (App M1 M2) <= maxvar (App M1 M2)) by eapply2 status_lt_maxvar. 
simpl in *. noway. 
(* 1 *) 
assert(combinator (App M1 M2) \/ (combinator (App M1 M2) -> False)) by eapply2 combinator_decidable. 
inversion H1. 
(* 2 *) 
exist (com_tag (App M1 M2)). 
eapply2 to_comb_int_compound_combinator. 
unfold_op; unfold com_tag; split_all. 
(* 1 *) 
assert(exists N, lamSF_red (App to_comb_int M1) N /\ combinator N). 
eapply2 IHnor1. 
simpl in *; omega. 
max_out. 
assert(exists N, lamSF_red (App to_comb_int M2) N /\ combinator N). 
eapply2 IHnor2. 
simpl in *; omega. 
max_out. 
split_all. 
exist(app_tag x0 x). 
apply transitive_red with (app_tag (App to_comb_int M1) (App to_comb_int M2)).
eapply2 to_comb_int_compound_not_combinator. 
simpl. unfold abs_left.
inversion H; split_all. 
unfold_op; repeat (eapply2 preserves_app_lamSF_red). 
unfold_op; split_all. 
repeat (eapply2 comb_app). 
Qed. 


Theorem abstract_to_comb_int : forall M, normal M -> maxvar M = 0 -> 
lamSF_red (App abstract (App to_comb_int M)) M. 
Proof. 
cut (forall p M, p >= rank M -> normal M -> maxvar M = 0 -> 
lamSF_red (App abstract (App to_comb_int M)) M). 
split_all. eapply2 H. 
induction p.
split_all. assert(rank M >0) by eapply2 rank_positive. noway. 
(* p > 0 *) 
intros M rnk nor; induction nor; split_all. 
(* 4 *) 
apply transitive_red with (App abstract (Op o)). 
eapply2 preserves_app_lamSF_red. 
eapply2 to_comb_int_op. 
eapply2 abstract_op. 
(* 3 *)
assert(maxvar M = 0 \/ maxvar M = 1) by omega. 
inversion H0. 
(* 4 *)
apply transitive_red with (App abstract (abs_tag (App to_comb_int(App k_op M)))).
eapply2 preserves_app_lamSF_red. 
eapply2 to_comb_int_abs_0. 
apply transitive_red with (App unstar (App abstract (App to_comb_int (App k_op M)))).
eapply2 abstract_abs_tag.
apply transitive_red with (App unstar (App k_op M)).
eapply2 preserves_app_lamSF_red. 
eapply2 IHp. 
simpl in *.  
assert(rank M > 0) by eapply2 rank_positive. 
omega. 
unfold_op; split_all.
unfold unstar. fold lamSF_red. fixtac.  fold unstar. unfold unstar_fn. eval_lamSF. 
 unfold subst_rec; fold subst_rec. insert_Ref_out. 
eval_lamSF. 
eval_lamSF. 
repeat (rewrite (subst_rec_closed equal_comb); [|split_all]). 
 unfold subst_rec ; fold subst_rec; insert_Ref_out. 
match goal with 
| |- _ _ (App (App _ ?M)?N) _ => 
apply transitive_red with (App (App (App k_op i_op) M) N)
end. 
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red. 
eapply2 unequal_closed_normal_forms; discriminate. 
eval_lamSF. eval_lamSF. 
match goal with 
| |- _ _ (App (App _ ?M)?N) _ => 
apply transitive_red with (App (App k_op M) N)
end. 
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red. 
eapply2 equal_closed_normal_forms; discriminate. 
eval_lamSF. 
repeat (rewrite (subst_rec_closed abs_K); [|split_all]). 
unfold abs_K. 
eval_lamSF. 
rewrite lift_rec_closed; split_all; omega. 
(* 3 *) 
apply transitive_red with (App abstract (abs_tag (App to_comb_int (star M)))). 
eapply2 preserves_app_lamSF_red. 
eapply2 to_comb_int_abs_1. 
apply transitive_red with (App unstar (App abstract (App to_comb_int (star M)))).
eapply2 abstract_abs_tag.
apply transitive_red with (App unstar (star M)).
eapply2 preserves_app_lamSF_red. 
eapply2 IHp. 
assert(rank (star M) < rank (Abs M)) by eapply2 rank_star. 
omega. 
eapply2 normal_star. 
assert(maxvar (star M) = pred (maxvar M)) by eapply2 maxvar_star. 
omega. 
eapply2 unstar_star. 
(* 2 *) 
assert(status (App M1 M2) <= maxvar (App M1 M2)) by eapply2 status_lt_maxvar. 
unfold maxvar in H1; fold maxvar in H1. 
noway. 
(* 1 *) 
assert(combinator (App M1 M2) \/ (combinator (App M1 M2) -> False)) by eapply2 combinator_decidable. 
inversion H1. 
(* 2 *) 
apply transitive_red with (App abstract(com_tag (App M1 M2))).
eapply2 preserves_app_lamSF_red. 
eapply2 to_comb_int_compound_combinator. 
eapply2 abstract_com_tag. 
apply transitive_red with (App abstract(app_tag (App to_comb_int (left_component (App M1 M2)))
                                 (App to_comb_int (right_component (App M1 M2))))). 
eapply2 preserves_app_lamSF_red. 
eapply2 to_comb_int_compound_not_combinator. 
unfold abs_tag; split_all. 
intro; subst. 
inversion H.
simpl. 
apply transitive_red with (App (App abstract(App to_comb_int M1))(App abstract(App to_comb_int M2))).
eapply2 abstract_app_tag. 
eapply2 preserves_app_lamSF_red. 
eapply2 IHnor1. simpl in *. omega. max_out. 
eapply2 IHnor2. simpl in *. omega. max_out. 
Qed. 
