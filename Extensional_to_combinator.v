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


(* to_combinator *) 

(* 
to_combinator := 
| O => O
| Abs M => to_combinator (star M)
| M N =>  (to_combinator M) (to_combinator N))

*) 

Fixpoint to_combinator_rank p M := 
match p with 
| 0 => M 
| S q => 
match M with 
| Ref n => Ref n 
| Op o => Op o 
| Abs M1 => to_combinator_rank q (star M1)
| App M1 M2 => App (to_combinator_rank q M1) (to_combinator_rank q M2)
end
end. 

Definition to_combinator M := to_combinator_rank (rank M) M. 



Lemma to_combinator_rank_stable: 
forall p q M, p>= q -> q >= rank M -> to_combinator_rank p M = to_combinator_rank q M. 
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
eapply2 IHp. omega. 
assert(rank(star l) < rank (Abs l)) by eapply2 rank_star. 
simpl in *. 
omega. 
(* 1 *) 
assert(q = S(pred q)) by omega. 
rewrite H1. simpl. 
rewrite (IHp (pred q) l); try omega. 
rewrite (IHp (pred q) l0); try omega. 
auto. 
Qed. 

Lemma to_combinator_abs: forall M, to_combinator (Abs M) = to_combinator (star M). 
Proof. 
split_all. 
unfold to_combinator, rank, to_combinator_rank; fold to_combinator_rank; fold rank. 
assert(rank M >0) by eapply2 rank_positive. 
assert(abs_rank * rank M = S (pred (abs_rank * rank M))).  
unfold abs_rank.  omega. 
rewrite H0. 
simpl. 
rewrite (to_combinator_rank_stable (pred
           (rank M +
            (rank M +
             (rank M +
              (rank M +
               (rank M +
                (rank M + (rank M + (rank M + (rank M + (rank M + 0))))))))))) (rank (star M)) (star M)). 
auto. 
assert(rank(star M) < rank (Abs M)) by eapply2 rank_star.
simpl in *. omega. 
auto. 
Qed.

Lemma to_combinator_app: 
forall M N, to_combinator (App M N) = App (to_combinator M) (to_combinator N).
Proof. 
split_all. 
unfold to_combinator, rank, to_combinator_rank; fold to_combinator_rank; fold rank. 
assert(rank M >0) by eapply2 rank_positive. 
assert(rank M + rank N = S (pred (rank M + rank N))) by omega. rewrite H0.
rewrite (to_combinator_rank_stable (S (pred (rank M + rank N))) (rank M)); try omega. 
rewrite (to_combinator_rank_stable (S (pred (rank M + rank N))) (rank N)); try omega. 
auto. 
Qed. 



Theorem to_combinator_makes_combinators : 
forall M, closed M -> combinator (to_combinator M). 
Proof. 
cut(forall p M, p >= rank M ->  closed M -> combinator (to_combinator M)). 
unfold closed; split_all. eapply2 H. induction p; split_all. assert(rank M >0) by eapply2 rank_positive.
noway. 
unfold closed in *; induction M; split_all.

(* 4 *) 
simpl in *. noway. 
(* 3 *) 
 unfold to_combinator, rank, to_combinator_rank; fold to_combinator_rank. split_all.  
(* 2 *)
rewrite to_combinator_abs. 
eapply2 IHp. 
assert(rank(star M) < rank (Abs M)) by eapply2 rank_star.
omega. 
rewrite maxvar_star. 
simpl in H0. auto. 
(* 1 *) 
 unfold to_combinator, rank, to_combinator_rank; fold to_combinator_rank; fold rank. 
simpl in *. max_out. 
eapply2 comb_app. 
rewrite (to_combinator_rank_stable (rank M1 + rank M2) (rank M1) M1); try omega.  
eapply2 IHM1. omega. 
rewrite (to_combinator_rank_stable (rank M1 + rank M2) (rank M2) M2); try omega.  
eapply2 IHM2. omega. 
Qed. 

Theorem to_combinator_is_extensional : 
forall M, beta_eta_eq M (to_combinator M). 
Proof. 
cut(forall p M, p >= rank M ->  beta_eta_eq M (to_combinator M)). 
split_all. eapply2 H. induction p. 
split_all; assert(rank M >0) by eapply2 rank_positive. noway. 
induction M; split_all.
(* 2 *) 
assert(beta_eta_eq (star M) (Abs M)). 
eapply2 star_equiv_abs.  
assert(beta_eta_eq (Abs M) (star M)). 
eapply2 symm_etared. 
assert(beta_eta_eq (star M) (to_combinator (star M))). 
eapply2 IHp. 
assert(rank(star M) < rank (Abs M)) by eapply2 rank_star. 
assert(rank M > 0) by eapply2 rank_positive. 
simpl in *; omega. 
assert( beta_eta_eq (to_combinator (star M)) (to_combinator (Abs M))). 
unfold to_combinator, to_combinator_rank; fold to_combinator_rank. 
assert(rank (Abs M) = S (pred (rank (Abs M)))). 
split_all. 
assert(rank M > 0) by eapply2 rank_positive. 
omega. 
rewrite H3. 
simpl. 
rewrite (to_combinator_rank_stable (pred
           (rank M +
            (rank M +
             (rank M +
              (rank M +
               (rank M +
                (rank M + (rank M + (rank M + (rank M + (rank M + 0))))))))))) (rank (star M))). 
auto. 
assert(rank (star M) < rank (Abs M)) by eapply2 rank_star. 
simpl in *. omega. auto. 
eauto. 
(* 1 *)
unfold to_combinator, to_combinator_rank; fold to_combinator_rank.
assert(rank(App M1 M2) = S (pred (rank (App M1 M2)))). 
assert(rank (App M1 M2) > 0) by eapply2 rank_positive. 
omega. 
rewrite H0. 
simpl in *.
eapply2 app_etared. 
rewrite (to_combinator_rank_stable (rank M1 + rank M2) (rank M1) M1); try omega.  
eapply2 IHM1. omega. 
rewrite (to_combinator_rank_stable (rank M1 + rank M2) (rank M2) M2); try omega.  
eapply2 IHM2. omega. 
Qed. 

Definition to_comb_fn := 
Abs (Abs  (App (App (App (Op Fop) (Ref 0)) (Ref 0)) (Abs (Abs 
(App (App (App (App equal abs_left) (Ref 1)) (App (Ref 3) (Ref 0)))
(App (App (Ref 3) (Ref 1)) (App (Ref 3) (Ref 0))))))))
.

Definition to_comb := App fixpoint to_comb_fn. 

Lemma to_comb_op : forall o, lamSF_red (App to_comb (Op o)) (Op o). 
Proof. 
split_all; unfold to_comb. fixtac. fold to_comb.  unfold to_comb_fn; unfold_op; repeat eval_lamSF. auto. 
Qed. 


Lemma to_comb_abs: forall M, normal M -> maxvar (Abs M) = 0 -> 
lamSF_red (App to_comb (Abs M)) (App to_comb (star M))
.
Proof. 
split_all; unfold to_comb. fixtac. unfold to_comb_fn at 1. fold to_comb. 
eval_lamSF. unfold subst_rec; fold subst_rec. insert_Ref_out. rewrite lift_rec_null. 
match goal with 
| |- multi_step lamSF_red1 (App (App (App (Op Fop) ?M) _) ?N) _ => 
  apply succ_red with (App (App N (left_component M)) (right_component M));
[eapply2 f_compound_lamSF_red|]
end.
assert(factorable (Abs M)).
eapply2 programs_are_factorable. split_all. 
inversion H1; split_all; subst;split_all. 
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
eapply2 equal_programs.
eval_lamSF. split_all. eval_lamSF.  
auto. 
Qed. 


Lemma to_comb_compound_combinator: forall M, compound M -> combinator M -> normal M ->
lamSF_red (App to_comb M)  (App (App to_comb (left_component M)) (App to_comb (right_component M)))
.
Proof. 
split_all; unfold to_comb. fixtac. unfold to_comb_fn at 1. fold to_comb. 
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
eapply2 unequal_programs. 
gen_inv H0 H; unfold_op; auto. subst. split_all.  eapply2 normal_component_l. 
assert(closed M) by eapply2 maxvar_combinator. 
gen_inv H2 H0. unfold closed in H5.  simpl in *.  max_out. 
gen_inv H H0; try discriminate. 
inversion H2. 
inversion H4; discriminate. 
eval_lamSF; eval_lamSF. 
repeat(rewrite (subst_rec_closed is_comb); try (split_all; omega)).
auto. 
Qed. 


Lemma to_comb_compound_not_abs: forall M, compound M -> left_component M <>abs_left -> normal M -> closed M ->
lamSF_red (App to_comb M) (App (App to_comb (left_component M)) (App to_comb  (right_component M)))
.
Proof. 
split_all; unfold to_comb. fixtac. unfold to_comb_fn at 1. fold to_comb. 
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
gen2_inv H0 H1 H.  
eapply2 unequal_programs; split_all. 
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
auto. 
Qed. 




Theorem to_combinator_to_comb:
forall M, program M -> lamSF_red (App to_comb M) (to_combinator M). 
Proof.
cut (forall p M, p >= rank M -> program M -> lamSF_red (App to_comb M) (to_combinator M)). 
split_all. eapply2 H. 
induction p.
split_all. assert(rank M >0) by eapply2 rank_positive. noway. 
(* p > 0 *) 
unfold program; intros M rnk prog; split_all.  induction H; split_all. 
(* 5 *)
inversion H0.  
(* 4 *) 
eapply2 to_comb_op. 
(* 3 *)
rewrite to_combinator_abs. 
assert(lamSF_red (App to_comb (Abs M)) (App to_comb (star M))). 
eapply2 to_comb_abs. 
assert(lamSF_red (App to_comb (star M)) (to_combinator (star M))) . 
eapply2 IHp. 
assert(rank(star M) < rank(Abs M)) by eapply2 rank_star. 
omega. 
split_all. eapply2 normal_star. rewrite maxvar_star. simpl in *. omega.
eapply transitive_red; eauto. 
(* 2 *) 
assert(status (App M1 M2) <= maxvar (App M1 M2)) by eapply2 status_lt_maxvar. 
simpl in *; noway. 
(* 1 *) 
assert(lamSF_red (App to_comb (App M1 M2)) (App (App to_comb M1) (App to_comb M2))). 
eapply2 to_comb_compound_not_abs.
inversion H; split_all. 
discriminate. 
discriminate. 
unfold abs_left; discriminate. 
subst. 
assert(status (App M0 M3) <= maxvar (App M0 M3)) by eapply2 status_lt_maxvar. 
simpl in *. max_out. 
(* 2 *) 
subst. 
inversion H2; subst. unfold abs_left; discriminate. 
(* 1 *) 
rewrite to_combinator_app. 
simpl in *. max_out. 
assert(lamSF_red (App to_comb M1) (to_combinator M1)). eapply2 IHp; try omega.  split_all. 
assert(lamSF_red (App to_comb M2) (to_combinator M2)). eapply2 IHp; try omega. split_all. 
eapply2 transitive_red; eauto.   
eapply2 preserves_app_lamSF_red. 
Qed. 


