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
(*                  LambdaFactor Calculus                             *)
(*                                                                    *)
(* is implemented in Coq by adapting the implementation of            *) 
(* Lambda Calculus from Project Coq                                   *) 
(* 2015                                                               *)
(**********************************************************************)

(**********************************************************************)
(*                      Equal.v                                       *)
(*                                                                    *)
(*                     Barry Jay                                      *)
(*                                                                    *)
(**********************************************************************)


Require Import ArithRing.
Require Import Max. 
Require Import Test.
Require Import General. 
Require Import Terms.
Require Import Lambda_tactics.
Require Import Substitution_term.
Require Import SF_reduction.
Require Import LamSF_reduction.
Require Import Normal.
Require Import Closed.
Require Import Eval.



(* General equality *) 

Definition is_atom M := 
  App (App (App (Op Fop) M) k_op) (App k_op (App k_op (App k_op i_op))).

Definition S_not_F M := App (App (App (App M (Op Fop)) k_op) k_op) i_op.

Lemma S_not_F_S : lamSF_red (S_not_F (Op Sop)) k_op. 
Proof. unfold i_op, k_op, S_not_F; repeat  eval_lamSF0; auto. Qed. 

Lemma S_not_F_F : lamSF_red (S_not_F (Op Fop)) (App k_op i_op). 
Proof. unfold i_op, k_op, S_not_F; repeat  eval_lamSF0; auto. Qed. 

Definition eq_op M N := iff (S_not_F M) (S_not_F N).

Definition equal_body :=  
(* Ref 2 is the recursion ref; 
   Ref 1 is the first argument, x
   Ref 0 is the second argument, y
*) 
App(App(App (Op Fop) (Ref 1))                       (* test x *) 
           (App(App(App (Op Fop) (Ref 0))            (* x an atom, test y *) 
                   (eq_op (Ref 1) (Ref 0)))        (* y an atom *) 
               (App k_op(App k_op(App k_op i_op))))) (* y compound *) 
   (Abs (Abs                                             (* x compound *) 
        (App(App(App (Op Fop) (Ref 2))            (* test y *) 
                (App k_op i_op))                   (* y an atom *) 
            (Abs (Abs     
                 (App(App(App(App(Ref 6)(Ref 3))(Ref 1))  (* left *) 
                                 (App(App(Ref 6)(Ref 2))(Ref 0)))(* right *) 
                             (App k_op i_op)))))))
.

Definition equal_fn := Abs (Abs (Abs equal_body)). 
Definition equal_comb :=  App fixpoint equal_fn.

Lemma equal_fn_closed: maxvar equal_fn = 0.
Proof. unfold equal_fn; split_all.  Qed. 
Lemma equal_comb_closed : maxvar equal_comb = 0.
Proof. split_all; omega. Qed. 

Ltac unfold_equal M N := 
unfold equal_comb at 1; eval_lamSF0; 
unfold equal_fn at 1; unfold equal_body;  unfold iff; unfold not.

Ltac eq_out := 
match goal with 
| |- _ >= maxvar equal_comb => unfold equal_comb; eq_out
| |- _ >= maxvar (App fixpoint equal_fn) => 
    rewrite equal_comb_closed; omega; eq_out 
| |- _ >= maxvar fixpoint => rewrite fixpoint_closed; omega; eq_out 
| |- _ >= maxvar equal_fn => rewrite equal_fn_closed; omega; eq_out 
| _ => try omega; auto
end.

Ltac eval_lamSF := eval_lamSF0;  relocate_lt; unfold insert_Ref; split_all.

Lemma equal_comb_op : forall o, lamSF_red (App (App equal_comb (Op o)) (Op o)) k_op.
Proof. 
split_all. 
unfold equal_comb at 1.  
apply transitive_red with 
(App (App (App equal_fn (App fixpoint equal_fn)) (Op o)) (Op o)). 
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red. 
eapply2 fixes. 
unfold equal_fn at 1; unfold equal_body, iff, not.
eval_lamSF. unfold subst; split_all. eval_lamSF. 
unfold lift; rewrite lift_rec_null. eval_lamSF. 
case o; repeat eval_lamSF; auto. 
Qed. 

Lemma unequal_op_compound : 
forall M o, compound M -> 
              lamSF_red (App (App equal_comb (Op o)) M) (App k_op i_op). 
Proof. 
split_all.
apply transitive_red with 
(App (App (App equal_fn (App fixpoint equal_fn)) (Op o)) M). 
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red. 
eapply2 fixes. 
unfold equal_fn at 1; unfold equal_body.
eval_lamSF.  eval_lamSF. 
unfold lift; rewrite lift_rec_null.
(* 1 *) 
match goal with 
| |- multi_step lamSF_red1 (App (App (App (Op Fop) ?M) _) ?N) _ => 

apply succ_red with (App (App N (left_component M)) (right_component M))
end.
eapply2 f_compound_lamSF_red.
eval_lamSF. 
Qed. 


Lemma unequal_op : 
forall M o, normal M -> maxvar M = 0 -> M <> (Op o) -> 
              lamSF_red (App (App equal_comb (Op o)) M) (App k_op i_op). 
Proof. 
split_all.
assert((exists o, M = (Op o)) \/ compound M) .
eapply2 not_active_factorable. 
assert(status M <= maxvar M) by eapply2 status_lt_maxvar. 
omega. 
inversion H2. 
2: eapply2 unequal_op_compound. 
split_all. subst. 
apply transitive_red with 
(App (App (App equal_fn (App fixpoint equal_fn)) (Op o)) (Op x)). 
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red. 
eapply2 fixes. 
unfold equal_fn at 1; unfold equal_body.
eval_lamSF.  eval_lamSF. 
unfold lift; rewrite lift_rec_null.
eval_lamSF.  
gen_case H1 x; gen_case H1 o; repeat (eval_lamSF). 
Qed. 



Lemma unequal_compound_op : 
forall M o, compound M -> 
              lamSF_red (App (App equal_comb M) (Op o))(App k_op i_op).
Proof. 
split_all.
apply transitive_red with 
(App (App (App equal_fn (App fixpoint equal_fn)) M) (Op o)) .
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red. 
eapply2 fixes. 
unfold equal_fn at 1; unfold equal_body.
eval_lamSF.  
unfold lift; rewrite lift_rec_null.
rewrite subst_rec_lift_rec; split_all. rewrite lift_rec_null. 
(* 3 *) 
match goal with 
| |- multi_step lamSF_red1 (App (App (App (Op Fop) M) _)?N) _ => 
apply succ_red with 
(App (App N (left_component M)) (right_component M))
end. 
eapply2 f_compound_lamSF_red. 
eval_lamSF. eval_lamSF. 
Qed. 

Lemma unequal_op2 : 
forall M o, normal M -> maxvar M = 0 -> M <> (Op o) -> 
              lamSF_red (App (App equal_comb M) (Op o))(App k_op i_op).
Proof. 
split_all.
assert((exists o, M = (Op o)) \/ compound M) .
eapply2 not_active_factorable. 
assert(status M <= maxvar M) by eapply2 status_lt_maxvar. 
omega. 
inversion H2. 
2: eapply2 unequal_compound_op. 
split_all. subst. 
apply transitive_red with 
(App (App (App equal_fn (App fixpoint equal_fn)) (Op x)) (Op o)). 
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red. 
eapply2 fixes. 
unfold equal_fn at 1; unfold equal_body.
eval_lamSF.  eval_lamSF. 
unfold lift; rewrite lift_rec_null.
eval_lamSF.  
gen_case H1 x; gen_case H1 o; repeat (eval_lamSF). 
Qed. 


Ltac eval_lamSF0 := unfold_op; 
match goal with 
| |-  lamSF_red ?M _ => red; eval_lamSF0
| |-  multi_step lamSF_red1 ?M _ =>
  (apply transitive_red with (eval0 M); 
[eapply2 eval0_from_lamSF |  
  unfold eval0, eval_app;  unfold subst; unfold subst_rec; fold subst_rec; fold eval_app; fold eval0])
| _ => auto
end.





Lemma equal_compounds : 
forall M N, compound M -> compound N -> 
lamSF_red (App (App equal_comb M) N) 
        (App (App 
                (App (App equal_comb (left_component M)) 
                     (left_component N))
                (App (App equal_comb (right_component M)) 
                     (right_component N)))
             (App k_op i_op))
.
Proof. 
split_all.
apply transitive_red with 
(App (App (App equal_fn (App fixpoint equal_fn)) M) N). 
app_lamSF. unfold equal_comb. eapply2 fixes. 
unfold equal_fn at 1; unfold equal_body. fold equal_comb. 
eval_lamSF0. insert_Ref_out; relocate_lt. eq_out. 
unfold subst_rec; fold subst_rec. 
insert_Ref_out. 
rewrite subst_rec_lift_rec. rewrite lift_rec_null. 
match goal with 
| |- multi_step lamSF_red1 (App (App (App (Op Fop) ?M) _) ?N) _ => 

apply succ_red with (App (App N (left_component M)) (right_component M)); split_all
end. 
eval_lamSF0. insert_Ref_out. 
rewrite subst_rec_lift_rec. 
rewrite subst_rec_lift_rec.  rewrite lift_rec_null. 
match goal with 
| |- multi_step lamSF_red1 (App (App (App (Op Fop) ?M) _) ?N) _ => 

apply succ_red with (App (App N (left_component M)) (right_component M)); split_all
end. 
eval_lamSF0. insert_Ref_out. 
relocate_lt. 
unfold subst_rec; fold subst_rec. 
insert_Ref_out. 
unfold subst_rec; fold subst_rec. 
insert_Ref_out. 
2: split_all. 2: split_all. 2: split_all. 2: split_all. 2: split_all. 2: split_all. 
repeat ((rewrite subst_rec_lift_rec); [|split_all]).  repeat(rewrite lift_rec_null). 
fold lamSF_red. 
app_lamSF. 
rewrite subst_rec_lift_rec. 
rewrite subst_rec_lift_rec. 
rewrite subst_rec_lift_rec. 
rewrite lift_rec_null. auto. 
split_all. split_all. split_all. split_all. split_all. split_all. 
rewrite subst_rec_lift_rec. 
rewrite lift_rec_null. auto. 
split_all. split_all. 
rewrite subst_rec_lift_rec. 
rewrite subst_rec_lift_rec. 
rewrite lift_rec_null. auto. 
split_all. split_all. split_all. split_all. 
Qed. 



Theorem equal_closed_normal_forms : 
forall M, normal M -> maxvar M = 0 -> 
lamSF_red (App (App equal_comb M) M) k_op
.
Proof. 
cut(forall p M, p >= rank M -> normal M -> maxvar M = 0 -> 
lamSF_red (App (App equal_comb M) M) k_op)
.
split_all. eapply2 H. 
induction p; split_all. 
assert(rank M >0) by eapply2 rank_positive. noway. 
(* p > 0 *) 
assert(status M <= maxvar M) by eapply2 status_lt_maxvar. 
assert((exists o, M = (Op o)) \/ compound M) . 
eapply2  not_active_factorable. omega. 
inversion H3; split_all; subst. 
eapply2 equal_comb_op.
apply transitive_red with 
(App (App (App (App equal_comb (left_component M)) (left_component M))
          (App (App equal_comb (right_component M)) (right_component M)))
     (App k_op i_op))
.
eapply2 equal_compounds. 

apply transitive_red with (App (App k_op k_op) (App k_op i_op)).
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red. 
(* left *) 
eapply2 IHp.  
assert(rank (left_component M) < rank M) by eapply2 rank_compound_l. 
omega. 
eapply2 normal_component_l. 
assert(maxvar (left_component M) <= maxvar M) by 
(eapply2 left_component_preserves_maxvar). 
omega. 
(* right *) 
eapply2 IHp.  
assert(rank (right_component M) < rank M) by eapply2 rank_compound_r. 
omega. 
eapply2 normal_component_r. 
assert(maxvar (right_component M) <= maxvar M) by 
(eapply2 right_component_preserves_maxvar). 
omega. 
(* 1*)
repeat eval_lamSF0; auto. 
Qed. 



Theorem unequal_closed_normal_forms : 
forall M N, normal M -> maxvar M = 0 -> normal N -> maxvar N = 0 -> 
M<>N ->  lamSF_red (App (App equal_comb M) N) (App k_op i_op)
.

Proof. 
cut(forall p  M N, p >= rank M -> normal M -> maxvar M = 0 -> 
normal N -> maxvar N = 0 ->  M<>N ->  lamSF_red (App (App equal_comb M) N) (App k_op i_op)
). 
split_all. eapply2 H. 
induction p; split_all. 
assert(rank M >0) by eapply2 rank_positive. noway. 
(* p > 0 *) 
assert(status M <= maxvar M) by eapply2 status_lt_maxvar. 
assert((exists o, M = (Op o)) \/ compound M) . 
eapply2  not_active_factorable. omega. 
inversion H6; split_all; subst. 
eapply2 unequal_op.
assert(status N <= maxvar N) by eapply2 status_lt_maxvar. 
assert((exists o, N = (Op o)) \/ compound N) . 
eapply2  not_active_factorable. omega. 
inversion H9; split_all;  subst. 
eapply2 unequal_op2.
(* both compounds *) 
apply transitive_red with 
(App (App (App (App equal_comb (left_component M)) (left_component N))
          (App (App equal_comb (right_component M)) (right_component N)))
     (App k_op i_op))
.
eapply2 equal_compounds. 

assert(left_component M = left_component N \/ left_component M <> left_component N) by eapply2 decidable_term_equality. 
assert(right_component M = right_component N \/ right_component M <> right_component N) by eapply2 decidable_term_equality. 
inversion H11.
inversion H12. 
(* 3 *) 
assert False. eapply2 H4. 
eapply2 components_monotonic. noway. 
(* 2 *) 
apply transitive_red with (App (App k_op (App k_op i_op)) (App k_op i_op)).
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red. 
rewrite H13. eapply2 equal_closed_normal_forms. 
eapply2 normal_component_l. 
assert(maxvar (left_component N) <= maxvar N) by 
(eapply2 left_component_preserves_maxvar). 
omega. 
eapply2 IHp.  
assert(rank (right_component M) < rank M) by eapply2 rank_compound_r. 
omega. 
eapply2 normal_component_r. 
assert(maxvar (right_component M) <= maxvar M) by 
(eapply2 right_component_preserves_maxvar). 
omega. 
eapply2 normal_component_r. 
assert(maxvar (right_component N) <= maxvar N) by 
(eapply2 right_component_preserves_maxvar). 
omega. 
repeat eval_lamSF0; auto. 
(* 2 *) 
apply transitive_red with (App (App (App k_op i_op) (App (App equal_comb (right_component M)) (right_component N))) (App k_op i_op)).
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red. 
eapply2 IHp.  
assert(rank (left_component M) < rank M) by eapply2 rank_compound_l. 
omega. 
eapply2 normal_component_l. 
assert(maxvar (left_component M) <= maxvar M) by 
(eapply2 left_component_preserves_maxvar). 
omega. 
eapply2 normal_component_l. 
assert(maxvar (left_component N) <= maxvar N) by 
(eapply2 left_component_preserves_maxvar). 
omega. 
unfold_op. 
eval_lamSF0. insert_Ref_out. relocate_lt.  auto. eval_lamSF0. auto.
Qed. 

