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
(*                      Closed.v                                      *)
(*                                                                    *)
(*                      Barry Jay                                     *)
(*                                                                    *)
(**********************************************************************)


Require Import Arith.
Require Import Lambda.Test.
Require Import Lambda.General. 
Require Import Omega.
Require Import Max. 
Require Import Lambda.Terms.
Require Import Lambda.Lambda_tactics.
Require Import Lambda.Substitution_term.

(* closed terms *) 


Fixpoint maxvar (M: lambda) := 
match M with 
| Ref i => S i
| App M1 M2 => max (maxvar M1) (maxvar M2)
| Abs N => pred (maxvar N) 
end.

Lemma maxvar_lift_rec : forall M n k, maxvar M + k >= maxvar (lift_rec M n k) .
Proof. 
induction M; split_all. 
unfold relocate. elim(test n0 n); split_all; omega. 
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


Definition decreases  (rank: lambda -> nat) (red:termred):= 
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

(* restore ?? 

Lemma decreases_maxvar_lamF_red1: decreases maxvar lambda_red1.
(* 
forall M N, lamF_red1 M N -> maxvar N <= maxvar M. 
*) 
Proof. 
cut(forall M N, lambda_red1 M N -> maxvar N <= maxvar M). 
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

Lemma decreases_maxvar_lamF_red : decreases maxvar lambda_red.
Proof. eapply2 decreases_multi_step. eapply2 decreases_maxvar_lamF_red1. Qed. 

*) 
