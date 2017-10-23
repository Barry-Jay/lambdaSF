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
(*              Extensional_to_combinator.v                           *)
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
Require Import Eta.
Require Import Extensional_to_combinator.
Require Import Unstar. 
Require Import Binding. 
Require Import Omega.

(* to_combinator_int *) 

(* 
to_combinator_int := 
| O => O
| Abs M => abs_tag (to_combinator_int (if binds (Abs M) then (star M) else (KM)))
| M N =>  if (is_combinator (M N)) then com (M N) else app (to_combinator_int M) (to_combinator_int N))

*) 



Fixpoint is_combinator_bool M := 
match M with 
| Op _ => true 
| App M1 M2 => andb (is_combinator_bool M1) (is_combinator_bool M2)
| _ => false
end. 

Lemma is_combinator_bool_true: forall M, combinator M -> is_combinator_bool M = true.
Proof. induction M; split_all; try (inversion H). 
rewrite IHM1; auto.   
Qed. 

Lemma  is_combinator_bool_false: forall M, (combinator M -> False) -> is_combinator_bool M = false.
Proof. induction M; split_all; try (assert False by eapply2 H; noway).
assert(combinator M1 \/ (combinator M1 -> False)) by eapply2 combinator_decidable. 
inversion H0; split_all.  
assert(combinator M2 \/ (combinator M2 -> False)) by eapply2 combinator_decidable. 
inversion H2; split_all.  
assert False by eapply2 H. noway. 
rewrite IHM2. 
case (is_combinator_bool M1); split_all. 
auto. 
rewrite IHM1. 
split_all. 
auto. 
Qed. 

Fixpoint to_combinator_int_rank p M := 
match p with 
| 0 => M 
| S q => 
match M with 
| Ref n => Ref n 
| Op o => Op o 
| Abs M1 => 
match maxvar M1 with 
| 0 => abs_tag (to_combinator_int_rank q (App k_op M1))
| _ => abs_tag (to_combinator_int_rank q (star M1))
end
| App M1 M2 => if (is_combinator_bool (App M1 M2)) 
               then com_tag (App M1 M2) 
               else app_tag (to_combinator_int_rank q M1) (to_combinator_int_rank q M2)
end
end. 

Definition to_combinator_int M := to_combinator_int_rank (rank M) M. 



Lemma to_combinator_int_rank_stable: 
forall p q M, p>= q -> q >= rank M -> to_combinator_int_rank p M = to_combinator_int_rank q M. 
Proof. 
induction p; split_all. 
assert(rank M >0) by eapply2 rank_positive. noway. 
gen_case H0 M. 
(* 4 *) 
assert(q = S(pred q)) by omega. 
rewrite H1. auto. 
(* 3 *) 
assert(q = S(pred q)) by omega. 
rewrite H1. auto. 
(* 2 *) 
assert(rank l > 0) by eapply2 rank_positive. 
assert(q = S(pred q)) by omega. 
rewrite H2. simpl. 
case (maxvar l); split_all. 
rewrite (IHp (pred q)). auto. omega. simpl. omega. 
rewrite (IHp (pred q)). auto. omega. 
assert(rank(star l) < rank (Abs l)) by eapply2 rank_star. 
simpl in *. 
omega. 
(* 1 *) 
assert(q = S(pred q)) by omega. 
rewrite H1. simpl. 
case (is_combinator_bool l); split_all. 
case (is_combinator_bool l0); split_all. 
rewrite (IHp (pred q) l); try omega. 
rewrite (IHp (pred q) l0); try omega. 
auto. 
rewrite (IHp (pred q) l); try omega. 
rewrite (IHp (pred q) l0); try omega. 
auto. 
Qed. 

Lemma to_combinator_int_abs_0: forall M, closed M -> to_combinator_int (Abs M) = abs_tag (to_combinator_int (App k_op M)). 
Proof. 
intros. 
unfold to_combinator_int at 1. 
unfold rank, to_combinator_int_rank; fold to_combinator_int_rank; fold rank. 
assert(rank M >0) by eapply2 rank_positive. 
assert(abs_rank * rank M = S (pred (abs_rank * rank M))).  
unfold abs_rank.  omega. 
rewrite H1. 
unfold to_combinator_int_rank at 1; fold to_combinator_int_rank.   
rewrite H. 
simpl. 
unfold to_combinator_int. 
rewrite (to_combinator_int_rank_stable (pred
           (rank M +
            (rank M +
             (rank M +
              (rank M +
               (rank M +
                (rank M + (rank M + (rank M + (rank M + (rank M + 0))))))))))) (rank (App k_op M))). 
auto. 
simpl; omega. 
omega. 
Qed.


Lemma to_combinator_int_abs_1: forall M, maxvar M = 1 -> to_combinator_int (Abs M) = abs_tag (to_combinator_int (star M)). 
Proof. 
intros. 
unfold to_combinator_int at 1. 
unfold rank, to_combinator_int_rank; fold to_combinator_int_rank; fold rank. 
assert(rank M >0) by eapply2 rank_positive. 
assert(abs_rank * rank M = S (pred (abs_rank * rank M))).  
unfold abs_rank.  omega. 
rewrite H1. 
unfold to_combinator_int_rank at 1; fold to_combinator_int_rank.   
rewrite H. 
unfold to_combinator_int. 
rewrite (to_combinator_int_rank_stable (pred (abs_rank * rank M)) (rank (star M))). 
auto. 
assert(rank (star M) < rank (Abs M)) by eapply2 rank_star. 
assert(rank M > 0) by eapply2 rank_positive. 
unfold abs_rank. 
simpl in *; omega. 
omega. 
Qed.


Lemma to_combinator_int_app_comb: 
forall M N, combinator (App M N) -> to_combinator_int (App M N) = com_tag (App M N).
Proof. 
split_all. 
unfold to_combinator_int, rank, to_combinator_int_rank; fold to_combinator_int_rank; fold rank. 
inversion H; split_all. 
assert(rank M >0) by eapply2 rank_positive. 
assert(rank M + rank N = S (pred (rank M + rank N))) by omega. 
rewrite is_combinator_bool_true. simpl. 
rewrite is_combinator_bool_true. auto. auto. auto. 
Qed. 


Lemma to_combinator_int_app_not_comb: 
forall M N, (combinator (App M N) -> False) -> 
to_combinator_int (App M N) = app_tag (to_combinator_int M) (to_combinator_int N).
Proof. 
split_all. 
unfold to_combinator_int, rank, to_combinator_int_rank; fold to_combinator_int_rank; fold rank. 
rewrite is_combinator_bool_false. 
assert(rank M >0) by eapply2 rank_positive. 
rewrite (to_combinator_int_rank_stable (rank M + rank N) (rank M)); try omega. 
rewrite (to_combinator_int_rank_stable (rank M + rank N)(rank N)); try omega. 
auto. auto. 
Qed. 


Theorem to_combinator_int_makes_combinators : 
forall M, maxvar M = 0 -> combinator (to_combinator_int M). 
Proof. 
cut(forall p M, p >= rank M ->  maxvar M = 0 -> combinator (to_combinator_int M)). 
split_all. eapply2 H. induction p; split_all. assert(rank M >0) by eapply2 rank_positive.
noway. 
induction M; split_all.

(* 4 *) 
simpl in *. noway. 
(* 3 *) 
 unfold to_combinator_int, rank, to_combinator_int_rank; fold to_combinator_int_rank. split_all.  
(* 2 *)
simpl in H0. 
assert(maxvar M = 0 \/ maxvar M = 1) by omega. 
inversion H1. 
(* maxvar M = 0 *) 
rewrite to_combinator_int_abs_0. 
unfold_op. 
repeat(eapply2 comb_app). 
assert(combinator M \/ (combinator M -> False)) by eapply2 combinator_decidable. 
inversion H3. 
rewrite to_combinator_int_app_comb. 
unfold_op. repeat(eapply2 comb_app). 
repeat(eapply2 comb_app). 
rewrite to_combinator_int_app_not_comb. 
repeat(eapply2 comb_app; unfold_op; auto). 
eapply2 IHM. 
simpl in *. 
omega. 
intro c; inversion c. 
assert False by eapply2 H4. 
noway. 
auto. 
(* maxvar M = 1 *) 
rewrite to_combinator_int_abs_1. 
unfold_op. 
repeat(eapply2 comb_app). 
eapply2 IHp. 
assert(rank (star M) < rank(Abs M)) by eapply2 rank_star. 
simpl in *; omega. 
rewrite maxvar_star. 
omega. 
auto.
(* 1 *) 
simpl in *; max_out. 
assert(combinator (App M1 M2) \/ (combinator (App M1 M2) -> False)) by eapply2 combinator_decidable. 
inversion H0. 
rewrite to_combinator_int_app_comb. 
unfold_op. repeat(eapply2 comb_app). 
auto. 
rewrite to_combinator_int_app_not_comb. 
repeat(eapply2 comb_app; unfold_op; auto). 
eapply2 IHM1. 
omega. 
eapply2 IHM2. omega. 
auto. 
Qed. 


Theorem to_combinator_int_is_extensional : 
forall M, maxvar M = 0 -> beta_eta_eq M (to_combinator_int M). 
Proof. 
cut(forall p M, p >= rank M ->  maxvar M = 0 -> beta_eta_eq M (to_combinator_int M)). 
split_all. eapply2 H. induction p. 
split_all; assert(rank M >0) by eapply2 rank_positive. noway. 
induction M; split_all.
(* 2 *) 
assert(maxvar M = 0 \/ maxvar M = 1) by omega. 
inversion H1. 
(* maxvar M = 0 *) 
rewrite to_combinator_int_abs_0. 
assert(beta_eta_eq (abs_tag  (to_combinator_int (App k_op M))) (to_combinator_int(App k_op M))). eapply2 tag_ext. 
assert(beta_eta_eq (to_combinator_int(App k_op M)) (App k_op M)). 
eapply2 symm_etared. 
eapply2 IHp. 
simpl. 
assert(rank M >0) by eapply2 rank_positive. 
omega. 
assert(beta_eta_eq (App k_op M) (Abs (App (lift_rec (App k_op M) 0 1) (Ref 0)))) by auto. 
simpl in *. 
rewrite lift_rec_closed in H5; try omega.  
assert( beta_eta_eq (Abs (App (App (App (Op Fop) (Op Fop)) M) (Ref 0))) (Abs M)).
auto. 
eauto. 
auto. 
(* maxvar M = 1 *) 
assert(beta_eta_eq (star M)(Abs M) ) . eapply2 star_equiv_abs. 
rewrite to_combinator_int_abs_1. 
assert(beta_eta_eq (abs_tag  (to_combinator_int (star M))) (to_combinator_int(star M))). eapply2 tag_ext. 
assert(beta_eta_eq (to_combinator_int(star M)) (star M)). 
eapply2 symm_etared. 
eapply2 IHp. 
eauto. 
assert(rank (star M) < rank (Abs M)) by eapply2 rank_star. 
simpl in *. 
omega. 
rewrite maxvar_star. omega. 
eauto.
auto. 
(* 1 *) 
max_out.
unfold to_combinator, to_combinator_rank; fold to_combinator_rank.
assert(combinator(App M1 M2) \/ (combinator(App M1 M2) -> False)) . 
eapply2 combinator_decidable. 
inversion H0. 
rewrite to_combinator_int_app_comb. 
eapply2 symm_etared. 
eapply2 tag_ext. 
auto. 
rewrite to_combinator_int_app_not_comb. 
assert(beta_eta_eq (app_tag (to_combinator_int M1) (to_combinator_int M2)) (wait (to_combinator_int M1) (to_combinator_int M2))). 
eapply2 tag_ext. 
assert(beta_eta_eq (wait (to_combinator_int M1) (to_combinator_int M2)) (App  (to_combinator_int M1) (to_combinator_int M2))). 
eapply2 wait_ext.
assert(beta_eta_eq (App  (to_combinator_int M1) (to_combinator_int M2)) (App M1 M2)).  
eapply2 app_etared. 
eapply2 symm_etared. eapply2 IHM1. omega. 
eapply2 symm_etared. eapply2 IHM2. omega. 
eauto. auto. 
Qed. 




Definition to_comb_int_fn := 
Abs (Abs  (App (App (App (Op Fop) (Ref 0)) (Ref 0)) (Abs (Abs 
(App (App (App (App equal abs_left) (Ref 1)) (abs_tag (App (Ref 3)
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
assert(factorable (Abs M)) . eapply2 programs_are_factorable; split_all; omega. 
inversion H1; split_all. 
eval_lamSF. 
repeat (rewrite (subst_rec_closed equal); [| split_all]). 
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
eapply2 equal_programs; split_all. 
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
eapply2 binds_star_0; split_all. 
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
repeat (rewrite (subst_rec_closed equal); [| split_all]). 
repeat (rewrite (subst_rec_lift_rec); [| split_all | split_all]). 
repeat (rewrite lift_rec_null).
insert_Ref_out. 
assert(factorable (Abs M)). eapply2 programs_are_factorable; split_all; omega. 
inversion H1; split_all. 
eval_lamSF. 
repeat (rewrite (subst_rec_closed equal); [| split_all]). 
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
eapply2 equal_programs; split_all; omega. 
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
repeat (rewrite (subst_rec_closed equal); [| split_all]). 
repeat (rewrite (subst_rec_lift_rec); [| split_all | split_all]). 
repeat (rewrite lift_rec_null).
match goal with
| |- multi_step lamSF_red1 (App (App _ ?M) ?N) _ => 
apply transitive_red with 
(App (App (App k_op i_op) M) N)
end.
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red.
eapply2 unequal_programs; split_all. eapply2 normal_component_l. 
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
eapply2 is_comb_true; split_all.  eapply2 maxvar_combinator. 
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
repeat (rewrite (subst_rec_closed equal); [| split_all]). 
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
eapply2 unequal_programs; split_all; omega. 
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
eapply2 unequal_programs; split_all; omega. 
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
eapply2 is_comb_false; split_all; omega. 
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

to_program:= 
| O => O 
| abs_tag _ M => unstar (to_program M) 
| com_tag M => M
| app_tag (wait M N) => (to_program M) (to_program N)
*) 


Definition to_prog_fn := 

Abs (Abs 
(App (App (App (Op Fop) (App untag (Ref 0))) (Ref 0)) (Abs (Abs 
(App (App (App (Op Fop) (Ref 1)) (Ref 1)) (Abs (Abs 
(App (App (App (App equal f_op) (Ref 0)) 
          (App unstar (App (Ref 5) (Ref 2))))
     (App (App (App (App equal s_op) (Ref 0)) (Ref 2)) 
          (App (App (App f_op (App unwait (Ref 2))) f_op) (Abs (Abs 
    (App (App (App f_op (Ref 1)) f_op) (Abs (Abs (App (App (Ref 9) (Ref 0)) (App (Ref 9) (Ref 2))))))
))))))))))))
.


Definition to_prog := App fixpoint to_prog_fn. 


Lemma to_prog_op : forall o, lamSF_red (App to_prog (Op o)) (Op o). 
Proof. 
split_all; unfold to_prog. fixtac. fold to_prog. 
unfold to_prog_fn. 
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


Lemma to_prog_abs_tag: 
forall M, lamSF_red (App to_prog (abs_tag M)) (App unstar (App to_prog M)). 
Proof. 
split_all; unfold to_prog. fixtac.  fold to_prog. unfold to_prog_fn. 
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
repeat (rewrite (subst_rec_closed equal); [|split_all]). 
 unfold subst_rec ; fold subst_rec; insert_Ref_out.
rewrite subst_rec_lift_rec; [|split_all|split_all]. 
match goal with 
| |- _ _ (App (App _ ?M)?N) _ => 
apply transitive_red with (App (App k_op M) N)
end. 
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red. 
eapply2 equal_programs; split_all; omega. 
eval_lamSF. 
repeat (rewrite (subst_rec_closed unstar); [| split_all]). 
repeat (rewrite (subst_rec_lift_rec to_prog); try omega). 
repeat (rewrite (subst_rec_lift_rec M); try omega). 
repeat (rewrite lift_rec_null). 
auto. 
Qed. 

Lemma to_prog_com_tag: forall M, lamSF_red (App to_prog (com_tag M)) M .
Proof. 
split_all; unfold to_prog. fixtac.  fold to_prog. unfold to_prog_fn. 
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
repeat (rewrite (subst_rec_closed equal); [|split_all]). 
 unfold subst_rec ; fold subst_rec; insert_Ref_out. 
repeat (rewrite (subst_rec_closed unstar); [|split_all]). 
repeat (rewrite (subst_rec_lift_rec to_prog); try omega).
match goal with 
| |- _ _ (App (App _ ?M)?N) _ => 
apply transitive_red with (App (App (App k_op i_op) M) N)
end. 
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red. 
eapply2 unequal_programs; split_all; omega. 
eval_lamSF. eval_lamSF. 
match goal with 
| |- _ _ (App (App _ ?M)?N) _ => 
apply transitive_red with (App (App k_op M) N)
end. 
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red. 
eapply2 equal_programs; split_all; omega. 
eval_lamSF. 
rewrite subst_rec_lift_rec; [|split_all|split_all]; try omega. 
rewrite subst_rec_lift_rec; [|split_all|split_all]; try omega. 
rewrite lift_rec_null.
auto.
Qed. 


Lemma to_prog_app_tag: 
forall M N, 
lamSF_red (App to_prog (app_tag M N))  (App (App to_prog M) (App to_prog N)).
Proof. 
split_all; unfold to_prog. fixtac.  fold to_prog. unfold to_prog_fn. 
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
repeat (rewrite (subst_rec_closed equal); [|split_all]). 
 unfold subst_rec ; fold subst_rec; insert_Ref_out. 
repeat (rewrite (subst_rec_closed unstar); [|split_all]). 
rewrite subst_rec_lift_rec; [|split_all|split_all]. 
match goal with 
| |- _ _ (App (App _ ?M)?N) _ => 
apply transitive_red with (App (App (App k_op i_op) M) N)
end. 
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red. 
eapply2 unequal_programs; split_all; omega. 
eval_lamSF. eval_lamSF. 
match goal with 
| |- _ _ (App (App _ ?M)?N) _ => 
apply transitive_red with (App (App (App k_op i_op) M) N)
end. 
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red. 
eapply2 unequal_programs; split_all; omega. 
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
repeat (rewrite (subst_rec_lift_rec to_prog); try omega). 
unfold subst_rec; fold subst_rec. 
insert_Ref_out. 
rewrite subst_rec_lift_rec; [|split_all|split_all]. 
rewrite subst_rec_lift_rec; [|split_all|split_all]. 
rewrite subst_rec_lift_rec; [|split_all|split_all]. 
repeat(rewrite lift_rec_null). 
auto.
Qed. 




Theorem to_comb_int_to_combinator_int:
forall M, program M -> lamSF_red (App to_comb_int M) (to_combinator_int M).
Proof.
cut (forall p M, p >= rank M -> program M -> lamSF_red (App to_comb_int M) (to_combinator_int M)). 
split_all. eapply2 H. 
induction p.
split_all. assert(rank M >0) by eapply2 rank_positive. noway. 
(* p > 0 *) 
unfold program; intros M rnk prg; split_all. induction H; split_all. 
(* 5 *) 
simpl in *; noway. 
(* 4 *) 
unfold to_combinator_int, to_combinator_int_rank; fold to_combinator_int_rank. simpl. 
eapply2 to_comb_int_op. 
(* 3 *)
simpl in H0. assert(maxvar M = 0 \/ maxvar M = 1) by omega. 
inversion H1. 
(* 4 *) 
rewrite to_combinator_int_abs_0.
apply transitive_red with (abs_tag  (App to_comb_int (App k_op M))). 
eapply2 to_comb_int_abs_0. 
unfold_op. 
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red. 
eapply2 IHp. 
split_all. simpl in *.  
assert(rank M > 0) by eapply2 rank_positive. 
omega. 
split_all; omega. auto. 
rewrite to_combinator_int_abs_1.
apply transitive_red with (abs_tag  (App to_comb_int (star M))). 
eapply2 to_comb_int_abs_1. 
unfold_op. 
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red. 
eapply2 IHp. 
split_all. simpl in *.  
assert(rank M > 0) by eapply2 rank_positive. 
assert(rank (star M) < rank (Abs M)) by eapply2 rank_star. simpl in *; omega. 
split_all.  eapply2 normal_star. rewrite maxvar_star. omega. auto. 
(* 2 *) 
assert(status (App M1 M2) <= maxvar (App M1 M2)) by eapply2 status_lt_maxvar. 
simpl in *. noway. 
(* 1 *) 
assert(combinator (App M1 M2) \/ (combinator (App M1 M2) -> False)) by eapply2 combinator_decidable. 
inversion H3. 
(* 2 *) 
rewrite to_combinator_int_app_comb. 
eapply2 to_comb_int_compound_combinator. auto. 
(* 1 *) 
rewrite to_combinator_int_app_not_comb. 
apply transitive_red with (app_tag (App to_comb_int M1) (App to_comb_int M2)). 
assert(M1 = left_component (App M1 M2)) by auto. 
assert(M2 = right_component (App M1 M2)) by auto. 
rewrite H5 at 2. 
rewrite H6 at 3. 
eapply2 to_comb_int_compound_not_combinator. inversion H2; discriminate. 
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red. 
unfold_op. 
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red. 
eapply2 IHnormal1. simpl in *; omega. simpl in *; max_out. 
eapply2 preserves_app_lamSF_red. 
eapply2 IHnormal2. simpl in *; omega. simpl in *; max_out. 
auto. 
Qed. 


Theorem to_comb_int_is_intensional : forall M, program M -> 
lamSF_red (App to_prog (App to_comb_int M)) M. 
Proof. 
cut (forall p M, p >= rank M -> program M -> 
lamSF_red (App to_prog (App to_comb_int M)) M). 
split_all. eapply2 H. 
induction p.
split_all. assert(rank M >0) by eapply2 rank_positive. noway. 
(* p > 0 *) 
unfold program; intros M rnk prg; split_all. induction H; split_all. 
(* 5 *) 
simpl in *; noway. 
(* 4 *) 
apply transitive_red with (App to_prog (Op o)). 
eapply2 preserves_app_lamSF_red. 
eapply2 to_comb_int_op. 
eapply2 to_prog_op. 
(* 3 *)
simpl in *; assert(maxvar M = 0 \/ maxvar M = 1) by omega. 
inversion H1. 
(* 4 *)
apply transitive_red with (App to_prog (abs_tag (App to_comb_int(App k_op M)))).
eapply2 preserves_app_lamSF_red. 
eapply2 to_comb_int_abs_0. 
apply transitive_red with (App unstar (App to_prog (App to_comb_int (App k_op M)))).
eapply2 to_prog_abs_tag.
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
repeat (rewrite (subst_rec_closed equal); [|split_all]). 
 unfold subst_rec ; fold subst_rec; insert_Ref_out. 
match goal with 
| |- _ _ (App (App _ ?M)?N) _ => 
apply transitive_red with (App (App (App k_op i_op) M) N)
end. 
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red. 
eapply2 unequal_programs; split_all; omega. 
eval_lamSF. eval_lamSF. 
match goal with 
| |- _ _ (App (App _ ?M)?N) _ => 
apply transitive_red with (App (App k_op M) N)
end. 
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red. 
eapply2 equal_programs; split_all; omega. 
eval_lamSF. 
repeat (rewrite (subst_rec_closed abs_K); [|split_all]). 
unfold abs_K, abs, ref.  
eval_lamSF. 
rewrite lift_rec_closed; split_all; omega. 
(* 3 *) 
apply transitive_red with (App to_prog (abs_tag (App to_comb_int (star M)))). 
eapply2 preserves_app_lamSF_red. 
eapply2 to_comb_int_abs_1. 
apply transitive_red with (App unstar (App to_prog (App to_comb_int (star M)))).
eapply2 to_prog_abs_tag.
apply transitive_red with (App unstar (star M)).
eapply2 preserves_app_lamSF_red. 
eapply2 IHp. 
assert(rank (star M) < rank (Abs M)) by eapply2 rank_star. 
simpl in *. omega. 
split_all.  eapply2 normal_star. 
assert(maxvar (star M) = pred (maxvar M)) by eapply2 maxvar_star. 
omega. 
eapply2 unstar_star. 
(* 2 *) 
assert(status (App M1 M2) <= maxvar (App M1 M2)) by eapply2 status_lt_maxvar. 
unfold maxvar in H1; fold maxvar in H1. 
noway. 
(* 1 *) 
assert(combinator (App M1 M2) \/ (combinator (App M1 M2) -> False)) by eapply2 combinator_decidable. 
inversion H3. 
(* 2 *) 
apply transitive_red with (App to_prog(com_tag (App M1 M2))).
eapply2 preserves_app_lamSF_red. 
eapply2 to_comb_int_compound_combinator. 
eapply2 to_prog_com_tag. 
apply transitive_red with (App to_prog(app_tag (App to_comb_int (left_component (App M1 M2)))
                                 (App to_comb_int (right_component (App M1 M2))))). 
eapply2 preserves_app_lamSF_red. 
eapply2 to_comb_int_compound_not_combinator. 
unfold abs_tag; split_all. 
intro; subst. 
inversion H2.
simpl. 
apply transitive_red with (App (App to_prog(App to_comb_int M1))(App to_prog(App to_comb_int M2))).
eapply2 to_prog_app_tag. 
eapply2 preserves_app_lamSF_red. 
eapply2 IHnormal1. simpl in *. omega. simpl in *; max_out. 
eapply2 IHnormal2. simpl in *. omega. simpl in *; max_out. 
Qed. 

