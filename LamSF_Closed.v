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
(* is implemented in Coq by adapting the implementation               *) 
(* of Lambda Calculus from Project Coq                                *)
(* 2015                                                               *)
(**********************************************************************)

(**********************************************************************)
(*                   LamSF_Closed.v                                   *)
(*                                                                    *)
(*                      Barry Jay                                     *)
(*                                                                    *)
(**********************************************************************)


Require Import Arith.
Require Import Test.
Require Import General. 
Require Import Max. 
Require Import LamSF_Terms.
Require Import LamSF_Tactics.
Require Import LamSF_Substitution_term.
Require Import SF_reduction.
Require Import LamSF_reduction.
Require Import LamSF_Normal.

(* closed terms *) 


Fixpoint maxvar (M: lamSF) := 
match M with 
| Ref i => S i
| Op o  => 0
| App M1 M2 => max (maxvar M1) (maxvar M2)
| Abs N => pred (maxvar N) 
end.

Definition closed M := maxvar M = 0. 

Lemma maxvar_lift_rec : forall M n k, maxvar M + k >= maxvar (lift_rec M n k) .
Proof. 
induction M; split_all. 
unfold relocate. elim(test n0 n); split_all; omega. 
omega. 
assert(pred (maxvar M) + k >= pred (maxvar M + k)) by omega.
assert(maxvar M + k >= maxvar (lift_rec M (S n) k)) by eapply2 IHM. 
omega.
rewrite max_plus. 
eapply2 max_monotonic. 
Qed. 

Lemma subst_decreases_maxvar : 
forall M N k,  max (pred (maxvar M)) (maxvar N + k) >= maxvar(subst_rec M N k).
Proof. 
induction M; split_all. 
unfold insert_Ref. 
elim(compare k n); split_all. 
elim a; split_all. 
assert(max n (maxvar N + k) >= n) by eapply2 max_is_max. 
omega. 
unfold lift. 
elim(maxvar_lift_rec N 0 k); split_all. 
eapply2 max_is_max. 
assert(max n (S m) >= max n m) by (eapply2 max_monotonic; omega). 
omega. 
assert(max n (maxvar N + k) >= maxvar N + k) by eapply2 max_is_max. 
omega. 
omega. 

(* 2 subgoals *) 
assert(max (pred (pred (maxvar M))) (maxvar N + k) >= pred(max (pred (maxvar M)) (maxvar N + (S k)))).
rewrite max_pred. 
eapply2 max_monotonic. 
omega.  
assert(max (pred (maxvar M)) (maxvar N + S k) >= maxvar (subst_rec M N (S k)))
by eapply2 IHM. 
assert(pred (max (pred (maxvar M)) (maxvar N + S k)) >= pred (maxvar (subst_rec M N (S k)))) by omega. 
omega. 
(* 1 *) 
rewrite max_pred. 
assert(max(max (pred (maxvar M1)) (maxvar N + k) ) (max (pred (maxvar M2)) (maxvar N + k)) >= max (maxvar (subst_rec M1 N k)) (maxvar (subst_rec M2 N k))).
eapply2 max_monotonic. 
assert(max (max (pred (maxvar M1)) (pred (maxvar M2))) (maxvar N + k)  >= 
max(max (pred (maxvar M1)) (maxvar N + k) ) (max (pred (maxvar M2)) (maxvar N + k))). 
2: omega. 
eapply2 max_max2; eapply2 max_monotonic; eapply2 max_is_max. 
Qed. 


Definition decreases  (rank: lamSF -> nat) (red:termred):= 
forall M N, red M N -> rank M >= rank N.

Lemma decreases_multi_step: 
forall rank red, decreases rank red -> decreases rank (multi_step red). 
Proof. 
red. intros rank red D M N R;  induction R; split_all. 
assert(rank M >= rank N) by eapply2 D. 
assert(rank N >= rank P) by eapply2 IHR. 
omega. 
Qed. 


Lemma lift_rec_closed: forall M n, n>= maxvar M  -> forall k, lift_rec M n k = M.
Proof. induction M; split_all; subst; unfold lift; unfold lift_rec; fold lift_rec. 
unfold relocate. elim(test n0 n); split_all; try noway. 
rewrite IHM.  auto. omega. 
assert(max (maxvar M1) (maxvar M2) >= maxvar M1) by eapply2 max_is_max. 
assert(max (maxvar M1) (maxvar M2) >= maxvar M2) by eapply2 max_is_max. 
rewrite IHM1; try omega; rewrite IHM2; try omega; congruence.
Qed. 

Lemma lift_closed: forall M, maxvar M =0 -> forall k, lift k M = M.
Proof.  split_all; eapply2 lift_rec_closed. omega. Qed. 


Lemma subst_rec_closed : forall M n, n>= maxvar M -> forall N, subst_rec M N n = M.
Proof.
induction M; split_all; subst.
unfold insert_Ref. 
elim(compare n0 n); split_all; try noway.  elim a; split_all; try noway. 
rewrite IHM; try omega; split_all. 
assert(max (maxvar M1) (maxvar M2) >= maxvar M1) by eapply2 max_is_max. 
assert(max (maxvar M1) (maxvar M2) >= maxvar M2) by eapply2 max_is_max. 
rewrite IHM1; try omega; rewrite IHM2; try omega; split_all. 
Qed. 

Lemma maxvar_subst_rec: forall M k, maxvar M <= k -> forall N, subst_rec M N k = M. 
Proof. 
induction M; unfold subst_rec; fold subst_rec; split_all; subst. 
unfold insert_Ref. elim(compare k n); split_all; try noway. 
elim a; split_all; try noway. 
rewrite IHM; split_all; omega. 

assert(k>= maxvar M1 /\ k>= maxvar M2) by eapply2 max_max; split_all. 
rewrite IHM1; split_all. 
rewrite IHM2; split_all. 
Qed. 

Lemma maxvar_star: forall M, maxvar (star M) = pred (maxvar M). 
Proof. 
induction M; split_all. 
case n; split_all. 
rewrite max_pred. auto.
Qed. 

Lemma left_component_preserves_maxvar : forall M, compound M -> 
maxvar(left_component M) <= maxvar M. 
Proof. 
split_all.
inversion H; split_all; try omega. 
eapply2 max_is_max.
Qed. 


Lemma right_component_preserves_maxvar : forall M, compound M -> 
maxvar(right_component M) <= maxvar M. 
Proof. 
split_all.
inversion H; split_all; try omega. 
eapply2 max_is_max. 
rewrite maxvar_star. 
auto. 
rewrite maxvar_star. 
auto. 
Qed. 

Ltac max_l := 
match goal with 
| |- max ?m ?n >= ?p => 
assert(max m n >= m) by eapply2 max_is_max; 
cut(m >= p); split_all; try omega
end. 
Ltac max_r := 
match goal with 
| |- max ?m ?n >= ?p => 
assert(max m n >= n) by eapply2 max_is_max; 
cut(n >= p); split_all; try omega
end. 



Lemma decreases_maxvar_lamF_red1: decreases maxvar lamSF_red1.
(* 
forall M N, lamF_red1 M N -> maxvar N <= maxvar M. 
*) 
Proof. 
cut(forall M N, lamSF_red1 M N -> maxvar N <= maxvar M). 
split_all; red. 

intros M N R; induction R; split_all; eauto; try (repeat (eapply2 max_monotonic); fail); try omega; repeat (eapply2 max_max2); try (max_r; fail); try (repeat max_l; fail). 
(* 5 *) 
unfold subst. 
assert(max (pred (maxvar M)) (maxvar N + 0) >= maxvar(subst_rec M N 0)).
eapply2 subst_decreases_maxvar. 
replace (maxvar N + 0) with (maxvar N) in H by omega. 
omega. 
(* 4 *) 
max_l. max_r. 
(* 3 *) 
assert(max(maxvar M) (maxvar N) >= maxvar M) by max_l. omega. 
(* 2 *) 
max_l. max_l. eapply2 left_component_preserves_maxvar.
max_l. max_l. eapply2 right_component_preserves_maxvar.
Qed. 

Lemma decreases_maxvar_lamF_red : decreases maxvar lamSF_red.
Proof. eapply2 decreases_multi_step. eapply2 decreases_maxvar_lamF_red1. Qed. 


Lemma status_lt_maxvar: forall M, status M <= maxvar M.  
Proof. 
cut(forall p M, p>= rank M -> status M <= maxvar M). 
split_all; eapply2 H. 
induction p; intros.  
assert(rank M >0) by eapply2 rank_positive. noway. 
induction M; intros; try max_out; try (eapply2 IHM1); try (split_all; omega). 
simpl in *; split_all. 
assert(status M <= maxvar M). eapply2 IHp. 
omega. omega. 
(* 1 *) 
generalize IHM1 H; clear IHM1 H; case M1; intros; try (split_all; omega). 
split_all. 
case (maxvar M2); split_all. 
assert(max n n0 >= n) by max_l. omega. 
(* 1 *) 
generalize IHM1 H; clear IHM1 H; case l; intros; try (split_all; omega). 
split_all. 
case (maxvar l0); split_all. 
case (maxvar M2); split_all. 
assert(max n n0 >= n) by max_l. omega. 
case (maxvar M2); split_all. 
assert(max n n0 >= n) by max_l. omega. 
assert(max n n0 >= n) by max_l. 
assert(max n n1 >= n) by max_l. 
assert(max (max n n0) n1 >= max n n1) by eapply2 max_monotonic. omega. 
(* 1 *) 
generalize IHM1 H; clear IHM1 H; case l1; intros; try (split_all; omega). 
split_all. 
case (maxvar l2); split_all. 
case (maxvar l0); split_all. 
case (maxvar M2); split_all. 
assert(max n n0 >= n) by max_l. omega. 
case (maxvar M2); split_all. 
assert(max n n0 >= n) by max_l. omega. 
assert(max n n0 >= n) by max_l. 
assert(max n n1 >= n) by max_l. 
assert(max (max n n0) n1 >= max n n1) by eapply2 max_monotonic. omega. 
case (maxvar l0); split_all. 
case (maxvar M2); split_all. 
assert(max n n0 >= n) by max_l. omega. 
assert(max n n0 >= n) by max_l. 
assert(max n n1 >= n) by max_l. 
assert(max (max n n0) n1 >= max n n1) by eapply2 max_monotonic. omega. 
case (maxvar M2); split_all. 
assert(max n n0 >= n) by max_l. 
assert(max n n1 >= n) by max_l. 
assert(max (max n n0) n1 >= max n n1) by eapply2 max_monotonic. omega. 
assert(max n n0 >= n) by max_l. 
assert(max n n1 >= n) by max_l. 
assert(max n n2 >= n) by max_l. 
assert(max (max n n0) n1 >= max n n1) by eapply2 max_monotonic. 
assert(max (max n n0) n1 >= n) by omega. 
assert(max (max (max n n0) n1) n2 >= max n n2) by eapply2 max_monotonic. 
assert(max (max (max n n0) n1) n2 >= n) by omega. 
omega. 
gen2_case IHM1 H o. 
omega. 
assert(status l2 <= maxvar l2). eapply2 IHp. simpl in *; omega. 
assert(maxvar l2 <= max (max (maxvar l2) (maxvar l0)) (maxvar M2)). 
assert(max (maxvar l2) (maxvar l0) >= maxvar l2) by max_l. 
assert(max (max (maxvar l2) (maxvar l0)) (maxvar M2) >= max (maxvar l2) (maxvar l0)) by max_l. 
omega. 
omega. 
(* 1 *) 
assert(status(App (App (App (App l3 l4) l2) l0) M2) = status  (App (App (App l3 l4) l2) l0)). split_all. 
rewrite H0.
assert(status (App (App (App l3 l4) l2) l0) <=
         maxvar (App (App (App l3 l4) l2) l0)). eapply2 IHM1. 
simpl in *; omega. 
assert(maxvar  (App (App (App l3 l4) l2) l0) <= maxvar (App (App (App (App l3 l4) l2) l0) M2)). split_all.  eapply2 max_is_max. omega. 
Qed. 

Definition program M := normal M /\ maxvar M = 0. 



Lemma components_monotonic: 
forall M N, program M -> program N ->  
left_component M = left_component N -> 
right_component M = right_component N -> M = N. 
Proof. 
induction M; unfold program; split_all. 
(* 3 *) 
gen4_case H1 H2 H3 H4 N; try discriminate.  
subst. gen_case H2 l. gen_case H2 n. discriminate. 
subst. inversion H3. inversion H7. inversion H7. 
(* 2 *) 
gen4_case H1 H2 H3 H4 N; try discriminate.  
(* 4 *) 
gen_case H2 M. 
gen_case H2 n. discriminate. 
assert(M=l). eapply2 star_monotonic. congruence. 
(* 2 *) 
subst. 
inversion H3. simpl in *. noway. 
inv1 compound. 
(* 1 *) 
inversion H0. simpl in *. 
assert(status (App M1 M2) <= maxvar (App M1 M2)) by eapply2 status_lt_maxvar. 
simpl in *. noway. 
subst. 
gen_case H9 N; inversion H9. 
Qed. 

Definition factorable M := (exists o, M = Op o) \/ compound M.

Theorem programs_are_factorable : forall M, program M  -> factorable M. 
Proof. 
unfold program, factorable; split_all. eapply2 not_active_factorable. 
assert(status M <= maxvar M) by eapply2 status_lt_maxvar. 
omega. 
Qed. 

