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
(App (App (App (App equal abs_left) (Ref 1)) (Abs (App (Ref 4) (App (Ref 3) (Ref 0)))))
(App (App (App (App equal k_op) (Ref 1)) (App abs_K (Ref 0)))
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
repeat (rewrite (subst_rec_closed equal);  [| split_all]). 
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
repeat (rewrite (subst_rec_closed equal);  [| split_all]). 
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
repeat (rewrite (subst_rec_closed equal);  [| split_all]). 
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
repeat (rewrite (subst_rec_closed equal);  [| split_all]).
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
repeat (rewrite (subst_rec_closed equal);  [| split_all]).
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
(App (App (App (App equal (left_component M)) (left_component N))
 (App (App equal (right_component M)) (right_component N)))
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
(App (App (App (App equal (left_component M)) (left_component N))
 (App (App equal (right_component M)) (right_component N)))
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
repeat (rewrite (subst_rec_closed equal);  [| split_all]).
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

Lemma wait_ext : forall M N, beta_eta_eq (wait M N) (App M N). 
Proof. 
split_all; unfold wait. 
assert(beta_eta_eq (App (App s_op (App (App s_op (App k_op M)) (App k_op N))) i_op)
(Abs (App (lift_rec (App (App s_op (App (App s_op (App k_op M)) (App k_op N))) i_op) 0 1) (Ref 0)))) by auto. 
simpl in *. 
assert(beta_eta_eq  (Abs
           (App
              (App
                 (App (Op Sop)
                    (App
                       (App (Op Sop)
                          (App (App (Op Fop) (Op Fop)) (lift_rec M 0 1)))
                       (App (App (Op Fop) (Op Fop)) (lift_rec N 0 1))))
                 (App (App (Op Sop) (App (Op Fop) (Op Fop)))
                    (App (Op Fop) (Op Fop)))) (Ref 0)))
(Abs (App (App (lift_rec M 0 1) (lift_rec N 0 1)) (Ref 0)))). 
eapply2 abs_etared.
assert(beta_eta_eq 
   (App
        (App
           (App (Op Sop)
              (App
                 (App (Op Sop) (App (App (Op Fop) (Op Fop)) (lift_rec M 0 1)))
                 (App (App (Op Fop) (Op Fop)) (lift_rec N 0 1))))
           (App (App (Op Sop) (App (Op Fop) (Op Fop)))
              (App (Op Fop) (Op Fop)))) (Ref 0))



        (App 
(App (App (App (Op Sop) (App (App (Op Fop) (Op Fop)) (lift_rec M 0 1)))
              (App (App (Op Fop) (Op Fop)) (lift_rec N 0 1))) (Ref 0))
        (App i_op (Ref 0)))).
auto. 
assert(beta_eta_eq 
(App
            (App
               (App
                  (App (Op Sop)
                     (App (App (Op Fop) (Op Fop)) (lift_rec M 0 1)))
                  (App (App (Op Fop) (Op Fop)) (lift_rec N 0 1))) 
               (Ref 0)) (App i_op (Ref 0)))
(App (App (App (App k_op (lift_rec M 0 1)) (Ref 0)) (App (App k_op (lift_rec N 0 1)) (Ref 0)))
(Ref 0))).
eapply2 app_etared.
unfold_op; auto. 
assert(beta_eta_eq   (App
        (App (App (Op Sop) (App (Op Fop) (Op Fop))) (App (Op Fop) (Op Fop)))
        (Ref 0)) (App (App k_op (Ref 0)) (App k_op (Ref 0)))).
auto.
assert(beta_eta_eq  (App (App k_op (Ref 0)) (App k_op (Ref 0))) (Ref 0)).  
unfold_op. eauto. 
eauto. 
assert(beta_eta_eq  (App
            (App (App (App k_op (lift_rec M 0 1)) (Ref 0))
               (App (App k_op (lift_rec N 0 1)) (Ref 0))) 
            (Ref 0))
(App (App (lift_rec M 0 1) (lift_rec N 0 1)) (Ref 0))). 
unfold_op. 
eapply2 app_etared.
eapply trans_etared. eexact H0. 
eapply trans_etared. eexact H1. 
eapply trans_etared. eexact H2. 
eauto. 
(* 1 *)
assert(beta_eta_eq (App M N) (Abs (App (lift_rec (App M N) 0 1) (Ref 0)))) by auto. 
simpl in *. 
eauto.  
Qed. 



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
