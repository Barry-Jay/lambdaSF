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
(*                       Quote.v                                      *)
(*                                                                    *)
(*                     Barry Jay                                      *)
(*                                                                    *)
(**********************************************************************)


Require Import Arith.
Require Import Max. 
Require Import Test.
Require Import General. 
Require Import Terms.
Require Import Closed.
Require Import Substitution_term.
Require Import Lambda_tactics.
Require Import SF_reduction.
Require Import Reduction.
Require Import Confluence.
Require Import LamSF_reduction.
Require Import Normal.
Require Import Eval.
Require Import Equal.

Ltac eval_lamSF := eval_lamSF0;  relocate_lt; unfold subst; unfold subst_rec; fold subst_rec; insert_Ref_out; repeat (rewrite lift_rec_null). 


(* unstar *) 



Lemma subst_rec_lift_rec2 : forall M n,
subst_rec (lift_rec M (S n) 1) (Ref 0) n = M. 
Proof. induction M; split_all. 
unfold relocate. 
elim(test (S n0) n); split_all. 
insert_Ref_out. auto. 
unfold insert_Ref. 
elim(compare n0 n); split_all. 
elim a; split_all. 
noway. 
unfold lift; split_all. 
relocate_lt. 
subst; auto. 
Qed. 

Definition abs_K := Abs (Abs (Ref 1)). 
Definition abs_S := 
Abs(Abs (Abs (App (App (Ref 2) (Ref 0)) (App (Ref 1) (Ref 0))))). 

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
(App (App (App (App equal_comb i_op) (Ref 1)) (Abs (App (Ref 4) (App (Ref 3) (Ref 0)))))
(App (App (App (App equal_comb k_op) (Ref 1)) (App abs_K (Ref 0)))
(App (App (App f_op (Ref 1)) (Ref 2)) (Abs (Abs 
(App (App abs_S (Ref 0)) (Ref 2))
)))))))))
.

Definition unstar := App fixpoint unstar_fn. 

Lemma unstar_star : forall M, normal M -> lamSF_red (App unstar (star M)) (Abs M). 
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
eapply2 unequal_closed_normal_forms. discriminate. 
eval_lamSF.  eval_lamSF.
match goal with 
| |- multi_step lamSF_red1 (App (App _ ?M)?N) _ => 
apply transitive_red with (App (App (App k_op i_op) M)N) 
end. 
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red. 
eapply2 unequal_closed_normal_forms. discriminate. 
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
eapply2 unequal_closed_normal_forms. discriminate. 
eval_lamSF.  eval_lamSF.
match goal with 
| |- multi_step lamSF_red1 (App (App _ ?M)?N) _ => 
apply transitive_red with (App (App k_op M)N) 
end. 
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red. 
eapply2 equal_closed_normal_forms. 
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
eapply2 unequal_closed_normal_forms. discriminate. 
eval_lamSF.  eval_lamSF.
match goal with 
| |- multi_step lamSF_red1 (App (App _ ?M)?N) _ => 
apply transitive_red with (App (App k_op M)N) 
end. 
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red. 
eapply2 equal_closed_normal_forms. 
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
eapply2 equal_closed_normal_forms. 
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
eapply2 unequal_closed_normal_forms. 
discriminate. 
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
eapply2 unequal_closed_normal_forms. 
discriminate. 
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

(* concrete *) 

(* 
Fixpoint delay n M := 
match n with 
| 0 => M 
| S n => wait i_op (delay n M)
end. 
*) 

(* 
concrete := 
| Abs M => S (concrete (star M))
| M N => S (concrete M) (concrete N) 
| O => K O

abstract:= 
| S M N => (abstract M) (abstract N)
| S M => unstar (abstract M) 
| K M => M 
| O => O 

OR

concrete := 
| Abs M => wait I (concrete (star M))
| M N => wait (id S) (concrete M) (concrete N) 
| O => wait (id F) O

abstract:= 
| wait I N => unstar (abstract M) 
| wait J M => M 
| wait M N => (abstract M) (abstract N)
| O => O 
*) 

Definition concrete_fn := 
Abs (Abs  (App (App (App (Op Fop) (Ref 0))  (wait (id f_op) (Ref 0))) (Abs (Abs 
(App (App (App (App equal_comb i_op) (Ref 1)) (wait i_op (App (Ref 3) (Ref 0))))
     (wait (id s_op) (wait (App (Ref 3) (Ref 1)) (App (Ref 3) (Ref 0)))))))))
.

Definition concrete := App fixpoint concrete_fn. 

Lemma concrete_op : forall o, lamSF_red (App concrete (Op o)) (wait (id f_op) (Op o)). 
Proof. 
split_all; unfold concrete. fixtac. 
unfold concrete_fn at 1; repeat eval_lamSF. auto. 
Qed. 


Lemma concrete_abs: forall M, compound (Abs M)-> 
lamSF_red (App concrete (Abs M)) (wait i_op (App concrete (star M)))
.
Proof. 
split_all; unfold concrete. fixtac. unfold concrete_fn at 1. fold concrete. 
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
simpl. insert_Ref_out. 
repeat (rewrite lift_rec_null).
match goal with
| |- multi_step lamSF_red1 (App (App _ ?M) ?N) _ => 
apply transitive_red with 
(App (App k_op M) N)
end.
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red. 
unfold_op. 
eapply2 equal_closed_normal_forms. 
eval_lamSF. auto. 
Qed. 


Lemma concrete_compound: forall M, compound M -> left_component M <> i_op -> 
lamSF_red (App concrete M) (wait (id s_op) (wait (App concrete (left_component M))
                                 (App concrete (right_component M))))
.
Proof. 
split_all; unfold concrete. fixtac. unfold concrete_fn at 1. fold concrete. 
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
gen_inv H0 H.
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
eval_lamSF. eval_lamSF. auto. 
Qed. 


(* unwait 

Definition wait M N := 
App (App s_op (App (App s_op (App k_op M)) (App k_op N))) i_op.

| wait M N => M N 


*) 

Definition unwait  := Abs (
App (App (App f_op (Ref 0)) (Ref 0)) (Abs (Abs (   (* P an operator or P = S (S(KM)(KN))I *) 
App (App (App f_op (Ref 1)) f_op) (Abs (Abs (   (* Ref 1 = S (S(KM)(KN)) *) 
App (App (App f_op (Ref 0)) f_op) (Abs (Abs (  (* Ref 1 = S, Ref 0 = S(KM)(KN) *) 
App (App (App f_op (Ref 1)) f_op) (Abs (Abs (  (* Ref 1 = S(KM), Ref 0 = KN *) 
App (App s_op
(App (App (App f_op (Ref 0)) f_op) (Abs (Abs (Ref 0))))) (* Ref 0 = KM *)
(App (App (App f_op (Ref 2)) f_op) (Abs (Abs (Ref 0)))) (* Ref 2 = KN *)
)))))))))))))
.

Lemma unwait_op : forall o, lamSF_red (App unwait (Op o)) (Op o). 
Proof. split_all. unfold unwait. unfold_op. eval_lamSF. eval_lamSF. auto. Qed.

Lemma unwait_wait : forall M N, lamSF_red (App unwait (wait M N)) (App (App s_op M) N). 
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
rewrite lift_rec_null. 
rewrite lift_rec_null. 
rewrite subst_rec_lift_rec; split_all.  
rewrite subst_rec_lift_rec; split_all.  
rewrite subst_rec_lift_rec; split_all.  
rewrite lift_rec_null. 
rewrite lift_rec_null.
eapply2 preserves_app_lamSF_red.  
eapply2 preserves_app_lamSF_red.  
eval_lamSF. 
unfold subst_rec; fold subst_rec. insert_Ref_out. 
eval_lamSF.
unfold subst_rec; fold subst_rec. insert_Ref_out. 
rewrite lift_rec_null. auto. 
eval_lamSF. eval_lamSF.
unfold subst_rec; fold subst_rec. insert_Ref_out. 
rewrite lift_rec_null. auto. 
Qed. 


(* 


abstract:= 
| wait I M => unstar (abstract M) 
| wait (id F) M => M 
| wait (id S) (wait M N) => (abstract M) (abstract N)
| O => O 

*) 

Definition abstract_fn := 

Abs (Abs 
(App (App (App (Op Fop) (App unwait (Ref 0))) (App unwait (Ref 0)))  (Abs (Abs 
(App (App (App (Op Fop) (Ref 1)) (Ref 1)) (Abs (Abs 
(App (App (App (App equal_comb (id f_op)) (Ref 0)) (Ref 2))
     (App (App (App (App equal_comb i_op) (Ref 0)) (App unstar (App (Ref 5) (Ref 2))))
     (App (App (App f_op (App unwait (Ref 2))) f_op) (Abs (Abs 
     (App (App (App f_op (Ref 1)) f_op) (Abs (Abs 
(App (App (Ref 9) (Ref 0)) (App (Ref 9) (Ref 2)))
))))))))))))))).

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
eapply2 unwait_op. 
eval_lamSF.
eapply2 unwait_op.  
omega. 
Qed. 


Lemma abstract_wait_id_F: 
forall M, lamSF_red (App abstract (wait (id f_op) M)) M. 
Proof. 
split_all; unfold abstract. fixtac.  fold abstract. unfold abstract_fn. 
eval_lamSF. unfold subst_rec ; fold subst_rec; insert_Ref_out. 
repeat (rewrite (subst_rec_closed unwait); [| split_all]). 
rewrite lift_rec_null.
match goal with 
| |- _ _ (App (App (App _ (App unwait ?M1))_)_) _ => 
replace M1 with (wait (id f_op) M) by split_all
end. 
match goal with 
| |- _ _ (App (App _ ?M1)?N1) _ => 
apply transitive_red with (App (App (App f_op (App (App s_op (id f_op)) M)) M1) N1)
end. 
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red. 
eapply2 unwait_wait. 
eval_lamSF. eval_lamSF.
 unfold subst_rec ; fold subst_rec; insert_Ref_out. 
eval_lamSF. eval_lamSF.
repeat (rewrite (subst_rec_closed equal_comb); [|split_all]). 
 unfold subst_rec ; fold subst_rec; insert_Ref_out. 
repeat (rewrite (subst_rec_closed unstar); [|split_all]). 
rewrite subst_rec_lift_rec; [|split_all|split_all]. 
match goal with 
| |- _ _ (App (App _ ?M)?N) _ => 
apply transitive_red with (App (App k_op M) N)
end. 
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red. 
eapply2 equal_closed_normal_forms. 
eval_lamSF. 
rewrite subst_rec_lift_rec; [|split_all|split_all]. 
rewrite lift_rec_null.
auto. 
omega. 
Qed. 


Lemma abstract_wait_I: 
forall M, lamSF_red (App abstract (wait i_op M)) (App unstar (App abstract M)). 
Proof. 
split_all; unfold abstract. fixtac.  fold abstract. unfold abstract_fn. 
eval_lamSF. unfold subst_rec ; fold subst_rec; insert_Ref_out. 
rewrite lift_rec_null. 
repeat (rewrite (subst_rec_closed unwait); [| split_all]). 
match goal with 
| |- _ _ (App (App (App _ (App unwait ?M1))_)_) _ => 
replace M1 with (wait i_op M) by split_all
end. 
match goal with 
| |- _ _ (App (App _ ?M1)?N1) _ => 
apply transitive_red with (App (App (App f_op (App (App s_op i_op) M)) M1) N1)
end. 
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red. 
eapply2 unwait_wait. 
eval_lamSF. eval_lamSF.
 unfold subst_rec ; fold subst_rec; insert_Ref_out. 
eval_lamSF. eval_lamSF.
repeat (rewrite (subst_rec_closed equal_comb); [|split_all]). 
 unfold subst_rec ; fold subst_rec; insert_Ref_out.
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
apply transitive_red with (App (App k_op M) N)
end. 
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red. 
eapply2 equal_closed_normal_forms; discriminate. 
eval_lamSF. 
repeat (rewrite (subst_rec_closed unstar); [|split_all]). 
eapply2 preserves_app_lamSF_red. 
rewrite subst_rec_lift_rec; [|split_all|split_all]. 
rewrite subst_rec_lift_rec; [|split_all|split_all]. 
rewrite subst_rec_lift_rec; [|split_all|split_all]. 
rewrite subst_rec_lift_rec; [|split_all|split_all]. 
rewrite subst_rec_lift_rec; [|split_all|split_all]. 
rewrite lift_rec_null.
rewrite subst_rec_lift_rec; [|split_all|split_all]. 
rewrite lift_rec_null.
auto. 
omega.
Qed. 

Lemma abstract_wait_S: 
forall M N, 
lamSF_red (App abstract (wait (id s_op) (wait M N)))
                      (App (App abstract M) (App abstract N)).  
Proof. 
split_all; unfold abstract. fixtac.  fold abstract. unfold abstract_fn. 
eval_lamSF. unfold subst_rec ; fold subst_rec; insert_Ref_out. 
rewrite lift_rec_null. 
repeat (rewrite (subst_rec_closed unwait); [|split_all]). 
rewrite lift_rec_null. 
match goal with 
| |- _ _ (App (App (App _ (App unwait ?M1))_)_) _ => 
replace M1 with (wait (id s_op) (wait M N)) by split_all
end. 
match goal with 
| |- _ _ (App (App _ ?M1)?N1) _ => 
apply transitive_red with (App (App (App f_op (App (App s_op (id s_op)) (wait M N))) M1) N1)
end. 
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red. 
eapply2 unwait_wait. 
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
rewrite lift_rec_null.
rewrite subst_rec_lift_rec; [|split_all|split_all]. 
rewrite subst_rec_lift_rec; [|split_all|split_all]. 
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
unfold subst_rec; fold subst_rec. 
rewrite subst_rec_lift_rec; [|split_all|split_all]. 
rewrite lift_rec_null. 
eval_lamSF. eval_lamSF. 
repeat (rewrite subst_rec_lift_rec; [|split_all; omega|split_all; omega]). 
rewrite lift_rec_null. 
rewrite lift_rec_null. 
unfold subst_rec; fold subst_rec. insert_Ref_out. rewrite lift_rec_null. 
auto. 
omega. 
Qed. 



Lemma abstract_concrete : forall M, normal M -> maxvar M = 0 -> 
lamSF_red (App abstract (App concrete M)) M. 
Proof. 
cut (forall p M, p >= rank M -> normal M -> maxvar M = 0 -> 
lamSF_red (App abstract (App concrete M)) M). 
split_all. eapply2 H. 
induction p.
split_all. assert(rank M >0) by eapply2 rank_positive. noway. 
(* p > 0 *) 
intros M rnk nor; induction nor; split_all. 
(* 4 *) 
apply transitive_red with (App abstract (wait (id f_op) (Op o))). 
eapply2 preserves_app_lamSF_red. 
eapply2 concrete_op. 
eapply2 abstract_wait_id_F. 
(* 3 *)
apply transitive_red with (App abstract (wait i_op (App concrete (star M)))). 
eapply2 preserves_app_lamSF_red. 
eapply2 concrete_abs. 
assert ((exists o, Abs M = Op o) \/ compound (Abs M)). 
eapply2 not_active_factorable. 
assert(status (Abs M) <= maxvar (Abs M)) by eapply2 status_lt_maxvar. 
simpl in *.
omega. 
inversion H0; split_all. 
apply transitive_red with (App unstar (App abstract (App concrete (star M)))).
eapply2 abstract_wait_I.
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
apply transitive_red with (App abstract(wait (id s_op) (wait (App concrete (left_component (App M1 M2)))
                                 (App concrete (right_component (App M1 M2)))))). 
eapply2 preserves_app_lamSF_red. 
eapply2 concrete_compound. 
simpl. 
intro; subst. 
inversion H.
simpl. 
apply transitive_red with (App (App abstract(App concrete M1))(App abstract(App concrete M2))).
eapply2 abstract_wait_S. 
eapply2 preserves_app_lamSF_red. 
eapply2 IHnor1. simpl in *. omega. max_out. 
eapply2 IHnor2. simpl in *. omega. max_out. 
Qed. 
