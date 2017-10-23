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
(*              Intensional Lambda Calculus                           *)
(*                                                                    *)
(* is implemented in Coq by adapting the implementation of            *) 
(* Lambda Calculus from Project Coq                                   *) 
(* 2015                                                               *)
(**********************************************************************)

(**********************************************************************)
(*                LamSF_Substitution_term.v                           *)
(*                                                                    *)
(*                     Barry Jay                                      *)
(*                                                                    *)
(* adapted from Substitution.v of Project Coq  to act on boa-terms    *)
(**********************************************************************)

Require Import Arith.
Require Import Test.
Require Import General.
Require Import LamSF_Terms.
Require Import LamSF_Tactics.
Require Import Omega.



(* Lifting lemmas *)

Lemma lift_rec_null_term : 
forall (U : lamSF)(n: nat), lift_rec U n 0 = U.
Proof. 
simple induction U; split_all.  
relocate_lt; auto.
Qed.

Lemma lift1 :
 forall (U : lamSF) (j i k : nat),
 lift_rec (lift_rec U i j) (j + i) k = lift_rec U i (j + k).
Proof.
simple induction U; simpl in |- *;  split_all. 
unfold relocate. 
elim (test i n); elim (test (j+i) (j+ n)); split_all; try noway. 
assert(k + (j + n) = j + k + n) by omega. congruence. 
elim (test (j + i) n); split_all; try noway. 

unfold relocate. 
replace (S(j+i)) with (j+ S i) by omega. 
rewrite H. auto. 
Qed. 

Lemma lift_lift_rec :
 forall (U : lamSF) (k p n i : nat),
 i <= n ->
 lift_rec (lift_rec U i p) (p + n) k = lift_rec (lift_rec U n k) i p.
Proof.
simple induction U; simpl in |- *;  split_all.
(* Ref *) 
unfold relocate.
elim(test i n); split_all; try noway. 
elim(test n0 n); split_all; try noway. 
elim(test (p+n0) (p+n)); split_all; try noway. 
elim(test i (k+n)); split_all; try noway. 
assert(k+(p+n) = p+ (k+n)) by omega. 
rewrite H0; auto. 
elim(test (p+n0) (p+n)); split_all; try noway. 
elim(test i n); split_all; try noway. 
elim(test n0 n); split_all; try noway. 
elim(test (p+n0) n); split_all; try noway. 
elim(test i n); split_all; try noway. 
(* Abs *) 
replace(S(p + n)) with (p + S n) by omega. 
rewrite H; split_all. omega. 
(* Ap *)
rewrite H; split_all.  rewrite H0; split_all. 
Qed. 


Lemma lift_lift_term :
 forall (U : lamSF) (k p n : nat),
 lift_rec (lift p U) (p+ n) k = lift p (lift_rec U n k).
Proof.
unfold lift in |- *; intros; apply lift_lift_rec; trivial with arith.
Qed.

Lemma liftrecO : forall (U : lamSF) (n : nat), lift_rec U n 0 = U.
Proof.
simple induction U; simpl in |- *; intros; split_all; relocate_lt; congruence. 
Qed.

Lemma liftO : forall (U : lamSF) , lift 0 U = U.
Proof.
unfold lift in |- *; split_all; apply liftrecO.
Qed.

Lemma lift_rec_lift_rec :
 forall (U : lamSF) (n p k i : nat),
 k <= i + n ->
 i <= k -> lift_rec (lift_rec U i n) k p = lift_rec U i (p + n).

Proof.
simple induction U; split_all.
(* Ref *) 
unfold relocate. 
elim(test i n); split_all; try noway. 
elim(test k (n0 + n)); split_all; try noway. 
replace (p+(n0+n)) with (p + n0 + n) by omega. auto. 
elim(test k n); split_all; try noway. 
(* Abs *) 
rewrite H; split_all; try omega. 
(* Ap *)
rewrite H; split_all; rewrite H0; split_all; split_all.
Qed. 

Lemma lift_rec_lift :
 forall (U : lamSF)  (n p k i : nat),
 k <= n -> lift_rec (lift  n U)  k p = lift (p + n) U.
Proof.
unfold lift in |- *; intros; rewrite lift_rec_lift_rec; trivial with arith.
Qed.



Lemma gt_plus : forall i m n : nat, i>m+n -> i> n.
Proof.
induction m.
simpl; tauto.
intros; apply (IHm); auto with arith.
Qed.

Lemma le_plus : forall i m n : nat, i +m <= n -> i<= n.
Proof.
induction m; intros. 
elim H;  auto with arith.
apply (IHm). 
apply le_trans with (i+S m).
auto with arith. trivial.

Qed.


Ltac lrlr_absurd p k n := 
absurd (p+S k> S n); [
apply le_not_gt;
replace (p+ S k) with (S (p+k)); auto with arith | trivial].


(* The three cases of substitution of U for (Ref n) *)

Lemma subst_eq :
 forall (M U : lamSF) (n : nat), subst_rec (Ref n) U n = lift n U. 
Proof.
simpl in |- *; unfold insert_Ref in |- *; split_all. 
elim (compare n n); intro P; try noway. 
elim P; intro Q; simpl in |- *; trivial with arith; try noway.
Qed.

Lemma subst_gt :
 forall (M U : lamSF) (n p : nat),
 n > p -> subst_rec (Ref n) U p = Ref (pred n).
Proof.
simpl in |- *; unfold insert_Ref in |- *.
intros; elim (compare p n); intro P.
elim P; intro Q; trivial with arith.
absurd (n > p); trivial with arith; rewrite Q; trivial with arith.
absurd (n > p); auto with arith.
Qed. 

Lemma subst_lt :
 forall (M U : lamSF) (n p : nat), p > n -> subst_rec (Ref n) U p = Ref n.
Proof.
simpl in |- *; unfold insert_Ref in |- *.
intros; elim (compare p n); intro P; trivial with arith.
absurd (p > n); trivial with arith; elim P; intro Q; auto with arith.
rewrite Q; trivial with arith.
Qed.

(* Substitution lemma *)

Lemma lift_rec_subst_rec :
 forall (V U : lamSF) (k p n : nat),
 lift_rec (subst_rec V U p) (p + n) k =
 subst_rec (lift_rec V (S (p + n)) k) (lift_rec U n k) p.
Proof.
simple induction V; split_all. 
(* 1 Ref *)
unfold insert_Ref, relocate in |- *.
elim (test (S(p + n0)) n); elim (compare p n); split_all.
elim a; elim(compare p (k+n)); split_all. 
unfold relocate. 
elim(test (p+n0) (pred n)); elim a1; split_all; try noway. 
replace (k + pred n) with (pred (k + n)) by omega; auto.
noway. 
noway. 
noway. 
noway. 
elim a; split_all.
unfold relocate. elim(test(p+n0) (pred n)); split_all. 
noway.
unfold lift.
rewrite lift_lift_rec; auto; omega. 
unfold relocate. 
elim(test (p+n0) n); split_all. 
noway. 
replace(S(p+n)) with (S p + n) by omega. 
congruence. 
Qed. 


Lemma lift_subst :
 forall (U V : lamSF) (k n : nat),
 lift_rec (subst U V) n k =
 subst (lift_rec U n k) (lift_rec V (S n) k).
Proof.
unfold subst in |- *; intros.
replace (S n) with (S (0 + n)).
elim lift_rec_subst_rec; trivial with arith.
simpl in |- *; trivial with arith.
Qed.

Lemma subst_rec_lift_rec1 :
 forall (U V : lamSF) (n p k : nat),
 k <= n ->
 subst_rec (lift_rec U k p) V (p + n) =
 lift_rec (subst_rec U V n) k p.
Proof.
simple induction U; intros; simpl in |- *; split_all.
(* Ref *) 
unfold insert_Ref, relocate. 
elim(test k n); split_all. 
elim(compare n0 n); split_all; try noway. 
elim a0; split_all; try noway. 
elim(compare (p+n0) (p+n)); split_all. 
elim a2; split_all; try noway. 
unfold relocate. 
elim(test k (pred n)); split_all; try noway. 
assert(pred (p+n) = p + pred n) by omega. auto. 
noway. 
elim(compare (p+n0) (p+n)); split_all. 
elim a1; split_all; try noway. 
unfold lift. rewrite lift_rec_lift_rec; split_all; try omega.  
unfold lift. rewrite lift_rec_lift_rec; split_all; try omega.  
elim(compare (p+n0) (p+n)); split_all. 
elim a0; split_all; try noway. 
unfold relocate. 
elim(test k n); split_all; try noway. 
elim(compare (p+n0) n); split_all; try noway. 
elim a; split_all; try noway. 
elim(compare n0 n); split_all; try noway. 
elim a; split_all; try noway. 
unfold relocate. 
elim(test k n); split_all; try noway. 

(* 2 subgoals *) 
replace (S(p + n)) with (p + S n) by omega.  
rewrite H; split_all; omega. 
(* 1 *) 
rewrite H; split_all.  rewrite H0; split_all. 
Qed. 

Lemma subst_rec_lift1 :
 forall (U V : lamSF) (n p : nat),
 subst_rec (lift p U) V (p + n) = lift p (subst_rec U V n).
Proof.
unfold lift in |- *; intros; rewrite subst_rec_lift_rec1;
 trivial with arith.
Qed.


Lemma subst_rec_lift_rec :
 forall (U V : lamSF) (p q n : nat),
 q <= p + n ->
 n <= q -> subst_rec (lift_rec U n (S p)) V q = lift_rec U n p.
Proof.
simple induction U; intros; simpl in |- *; split_all. 
unfold relocate. elim(test n0 n); split_all. 
unfold insert_Ref. 
elim(compare q (S(p+n))); split_all; try noway. 
elim a0; split_all; try noway. 
unfold insert_Ref. 
elim(compare q n); split_all; try noway. 
elim a; split_all; try noway. 

(* 2 *)
rewrite H; auto; omega. 
(* 1 *) 
rewrite H; split_all. 
rewrite H0; auto.
Qed.

(* subst_rec_subst_rec *)

Lemma subst_rec_subst_rec :
 forall (V U W : lamSF) (n p : nat),
 subst_rec (subst_rec V U p) W (p + n) =
 subst_rec (subst_rec V W (S (p + n))) (subst_rec U W n) p.
Proof.
simple induction V;  split_all.

unfold insert_Ref in |- *.
elim (compare p n); split_all. 
elim a; split_all. 
elim (compare (S (p + n0)) n); split_all. 
elim a1; split_all; try noway. 
unfold insert_Ref.
elim (compare (p+n0) (pred n)); split_all; try noway. 
elim a3; split_all; try noway.
elim (compare p (pred n)); split_all; try noway. 
elim a5; split_all; try noway.
unfold lift; split_all. 
unfold insert_Ref. 
elim (compare (p+n0) (pred n)); split_all; try noway. 
elim a2; split_all; try noway.
subst. unfold lift. 
rewrite subst_rec_lift_rec; split_all; try omega. 
unfold insert_Ref. 
elim(compare (p+n0) (pred n)); split_all; try noway. 
elim a1; split_all; try noway. 
elim(compare p n); split_all; try noway. 
elim a1; split_all; try noway. 
elim (compare (S (p + n0)) n); split_all; try noway. 
elim a0; split_all; try noway.
unfold insert_Ref. 
elim(compare p n); split_all; try noway. 
elim a0; split_all; try noway. 
unfold lift. 
subst. 
rewrite subst_rec_lift_rec1; split_all.  omega. 

unfold insert_Ref. 
elim(compare (p+n0) n); split_all; try noway. 
elim a; split_all; try noway.
elim(compare (S(p+n0)) n); split_all; try noway. 
elim a; split_all; try noway. 
unfold insert_Ref. 
elim(compare p n); split_all; try noway. 
elim a; split_all; try noway. 

replace(S(p + n)) with (S p + n) by omega. 
rewrite H; split_all; omega. 
Qed.


Lemma subst_rec_subst_0 :
 forall (U V W : lamSF) (n : nat),
 subst_rec (subst_rec V U 0) W n =
 subst_rec (subst_rec V W (S n)) (subst_rec U W n) 0.
Proof.
intros; pattern n at 1 3 in |- *.
replace n with (0 + n) by trivial with arith.
rewrite (subst_rec_subst_rec V U W n 0); trivial with arith.
Qed.

(**************************)
(* The Substitution Lemma *)
(**************************)

Lemma substitution :
 forall (U V W : lamSF) (n : nat),
 subst_rec (subst U V) W n =
 subst (subst_rec U W n) (subst_rec V W (S n)).
Proof.
unfold subst in |- *; intros; apply subst_rec_subst_0; trivial with arith.
Qed.

(* to show (\ t)0 -> t  *) 


Lemma lift_rec_null : 
forall (U : lamSF) (n: nat), lift_rec U n 0 = U.
Proof. simple induction U; split_all.
 rewrite relocate_null; congruence.
Qed.

Lemma subst_lift_null :
forall (W V : lamSF)(n : nat), subst_rec (lift_rec W n 1) V n = W.
Proof.
simple induction W; split_all. 
unfold insert_Ref. 
unfold relocate. 
elim(test n0 n); split_all. 
elim(compare n0 (S n)); split_all.
elim a0; split_all; noway. 
noway. 
elim(compare n0 n); split_all.
elim a; split_all. noway. 
noway.
Qed. 


(* more  Properties *) 

Lemma lift_rec_lift2 : 
forall M n k, lift_rec (lift 1 M) (S n) k = lift 1 (lift_rec M n k).
Proof.
split_all.
unfold lift. 
replace (S n) with (1+n) by omega.
rewrite lift_lift_rec; auto. 
omega.
Qed.

Lemma relocate_null2 :
forall n k, relocate 0 (S n) k = 0.
Proof. split_all. Qed. 

Lemma subst_rec_lift2 : 
forall M N n , subst_rec (lift 1 M) N (S n)  = lift 1 (subst_rec M N n).
Proof.
split_all.
unfold lift. 
replace (S n) with (1+n) by omega.
rewrite subst_rec_lift_rec1; auto. 
omega.
Qed.



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
