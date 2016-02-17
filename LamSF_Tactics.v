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
(*             Intensional Lambda Calculus                            *)
(*                                                                    *)
(* is implemented in Coq by adapting the implementation of            *)
(* Lambda Calculus from Project Coq                                   *)
(* 2015                                                               *)
(**********************************************************************)

(**********************************************************************)
(*                   LamSF_tactics.v                                  *)
(*                                                                    *)
(*                     Barry Jay                                      *)
(*                                                                    *)
(**********************************************************************)

Require Import Arith.
Require Import Test. 
Require Import General.
Require Import LamSF_Terms. 

Definition termred := lamSF -> lamSF -> Prop.

Definition preserve (R : termred) (P : lamSF -> Prop) :=
  forall x : lamSF, P x -> forall y : lamSF, R x y -> P y.


Inductive multi_step : termred -> termred :=
  | zero_red : forall red M, multi_step red M M
  | succ_red : forall (red: lamSF-> lamSF -> Prop) M N P, 
                   red M N -> multi_step red N P -> multi_step red M P
.

Inductive sequential : termred -> termred -> termred :=
  | seq_red : forall (red1 red2 : termred) M N P, 
                red1 M N -> red2 N P -> sequential red1 red2 M P.

Hint Resolve zero_red succ_red seq_red
.

Definition reflective red := forall (M: lamSF), red M M.

Lemma refl_multi_step : forall (red: termred), reflective (multi_step red).
Proof. red; split_all. Qed.

Lemma refl_seq : forall (red1 red2: termred),
                   reflective red1 -> reflective red2 -> reflective(sequential red1 red2).
Proof. red; split_all; eapply2 seq_red. Qed.


Ltac reflect := match goal with 
| |- reflective (multi_step _) => eapply2 refl_multi_step
| |- multi_step _ _ _ => try (eapply2 refl_multi_step)
| |- reflective (sequential _) => eapply2 refl_seq; reflect 
| |- sequential _ _ _ _ => try (eapply2 refl_seq)
| _ => split_all
end.


Ltac one_step := 
match goal with 
| |- multi_step _ _ ?N => apply succ_red with N; auto; try red; try reflect
end.

Ltac seq_l := 
match goal with 
| |- sequential _ _ ?M ?N => apply seq_red with N; auto; red; reflect
end.

Ltac seq_r := 
match goal with 
| |- sequential _ _ ?M ?N => apply seq_red with M; auto; red; reflect
end.


Definition transitive red := forall (M N P: lamSF), red M N -> red N P -> red M P. 

Lemma transitive_red : forall red, transitive (multi_step red). 
Proof. red; induction 1; split_all. 
apply succ_red with N; auto. 
Qed. 

Definition preserves_abs (red : termred) := 
forall M N, red M N -> red (Abs M) (Abs N).

Definition preserves_app (red : termred) := 
forall M M' N N', red M M' -> red N N' -> red (App M N) (App M' N').

Lemma preserves_abs_multi_step : forall red, preserves_abs red -> preserves_abs (multi_step red). 
Proof.
red; induction 2; split_all.
apply succ_red with (Abs N); auto.
Qed.

Lemma preserves_app_multi_step : forall (red: termred), reflective red -> preserves_app red -> preserves_app (multi_step red). 
Proof.
red. induction 3; split_all. generalize H0; induction 1. 
reflect. 
apply succ_red with (App M N); auto.
assert( transitive (multi_step red)) by eapply2 transitive_red.  
apply X0 with (App N0 N); auto. 
one_step. 
Qed.

Lemma preserves_abs_seq : forall (red1 red2: termred), preserves_abs red1 -> preserves_abs red2 -> preserves_abs (sequential red1 red2). 
Proof.
red; split_all.
inversion H1.
apply seq_red with (Abs N0); auto.
Qed.

Lemma preserves_app_seq : forall (red1 red2: termred), preserves_app red1 -> preserves_app red2 -> preserves_app (sequential red1 red2). 
Proof.
red; split_all. 
inversion H1; inversion H2.
apply seq_red with (App N0 N1); auto.
Qed.

Hint Resolve preserves_abs_multi_step  preserves_app_multi_step preserves_abs_seq preserves_app_seq .



Definition preserves_abs1 (red: termred) := forall M N, red M N -> forall M0, M = Abs M0 -> 
  exists N0, red M0 N0 /\ Abs N0 = N.

Lemma preserves_abs1_multi_step : forall red, preserves_abs1 red -> preserves_abs1 (multi_step red).
Proof. 
unfold preserves_abs1.  induction 2; split_all. 
exist M0. 
assert(exists N0 : lamSF, red M0 N0 /\ Abs N0 = N) by eapply2 H; split_all.
assert(exists N0 : lamSF, multi_step red x N0 /\ Abs N0 = P) by eapply2 IHmulti_step; split_all.
exist x0. 
apply succ_red with x; auto.
Qed.

Lemma preserves_abs1_seq : forall red1, preserves_abs1 red1 -> forall red2, preserves_abs1 red2 -> preserves_abs1 (sequential red1 red2).
Proof. 
unfold preserves_abs1; split_all. 
inversion H1.
elim(H M N0 H3 M0); split_all.
elim(H0 N0 N H4 x); split_all.
exist x0.
apply seq_red with x; auto.
Qed.

Hint Resolve preserves_abs1_multi_step preserves_abs1_seq.

Definition lift_rec_preserves (red: termred) := 
forall (M N : lamSF), red M N -> forall (n k : nat), red  (lift_rec M n k) (lift_rec N n k).


Lemma lift_rec_preserves_multi_step : 
forall red, lift_rec_preserves red -> lift_rec_preserves (multi_step red). 
Proof. unfold lift_rec_preserves; induction 2; split_all.  
apply succ_red with (lift_rec N n k); auto.
Qed.

Lemma lift_rec_preserves_seq : 
forall red1 red2, lift_rec_preserves red1 -> lift_rec_preserves red2 -> 
                  lift_rec_preserves (sequential red1 red2). 
Proof. red; unfold lift_rec_preserves; split_all.  
inversion H1. apply seq_red with (lift_rec N0 n k); auto.
Qed.

Hint Resolve  lift_rec_preserves_multi_step lift_rec_preserves_seq.



Definition preserves_lift_rec (red: lamSF ->  lamSF -> Prop) := 
forall M N, red M N -> forall M0 n k, lift_rec M0 n k = M -> exists N0, red M0 N0 /\ lift_rec N0 n k = N. 

Lemma preserves_lift_rec_multi_step : 
forall red, preserves_lift_rec red -> preserves_lift_rec (multi_step red).
Proof. unfold preserves_lift_rec. induction 2; split_all. 
exist M0. 
elim(H M N H0 M0 n k); split_all.
elim(IHmulti_step H x n k); split_all.
exist x0.
apply succ_red with x; auto.
Qed. 

Lemma preserves_lift_rec_seq : 
forall red1, preserves_lift_rec red1 -> forall red2, preserves_lift_rec red2 -> 
                                                     preserves_lift_rec (sequential red1 red2).
Proof. unfold preserves_lift_rec. induction 3; split_all. 
elim(H M N H1 M0 n k); split_all.
elim(H0 N P H2 x n k); split_all.
exist x0.
apply seq_red with x; auto.
Qed. 


Ltac eelim_for_equal := 
match goal with 
| H: forall _, _ = _ -> _  |- _ => eelim H; clear H; subst; eelim_for_equal
| _ => split_all 
end. 

Ltac inv_lift_rec := 
match goal with 
| H: Ref _ = lift_rec ?l _ _  |- _ => gen_case_inv H l; inv_lift_rec
| H: Op _ = lift_rec ?l _ _  |- _ => gen_case_inv H l; inv_lift_rec
| H: App _ _ = lift_rec ?l _ _ |- _ => gen_case_inv H l; inv_lift_rec
| H: Abs _ = lift_rec ?l _ _ |- _ => gen_case_inv H l; inv_lift_rec
| H: lift_rec ?l _ _ = Ref _ |- _ => gen_case_inv H l; inv_lift_rec
| H: lift_rec ?l _ _ = Op _ |- _ => gen_case_inv H l; inv_lift_rec
| H: lift_rec ?l _ _ = App _ _ |- _ => gen_case_inv H l; inv_lift_rec
| H: lift_rec ?l _ _ = Abs _ |- _ => gen_case_inv H l; inv_lift_rec
| _ => subst; eelim_for_equal
 end.

Ltac inv1 prop := 
match goal with 
| H: prop (Ref _) |- _ => inversion H; clear H; inv1 prop
| H: prop (App  _ _) |- _ => inversion H; clear H; inv1 prop
| H: prop Op _ |- _ => inversion H; clear H; inv1 prop
| H: prop (Abs _) |- _ => inversion H; clear H; inv1 prop
| _ => split_all
 end.


Definition implies_red (red1 red2: termred) := forall M N, red1 M N -> red2 M N. 

Lemma implies_red_multi_step: forall red1 red2, implies_red red1  (multi_step red2) -> 
                                                implies_red (multi_step red1) (multi_step red2).
Proof. red. 
intros red1 red2 IR M N R; induction R; split_all. 
apply transitive_red with N; auto. 
Qed. 
Lemma implies_red_seq: 
 forall red1 red2 red3, 
  implies_red red1  (multi_step red3)  ->  
  implies_red red2 (multi_step red3) -> 
  implies_red (sequential red1 red2) (multi_step red3) .
Proof. 
red; split_all. inversion H1. apply transitive_red with N0; auto. 
Qed. 


Definition subst_rec_preserves_l (red: termred) := 
forall (M M' N : lamSF), red M M' -> forall ( k : nat), red  (subst_rec M N k) (subst_rec M' N k).

Definition subst_rec_preserves_r (red: termred) := 
forall (M N N' : lamSF), red N N' -> forall ( k : nat), red  (subst_rec M N k) (subst_rec M N' k).

Definition subst_rec_preserves (red: termred) := 
forall (M M' : lamSF), red M M' -> forall N N', red N N' -> forall ( k : nat), red  (subst_rec M N k) (subst_rec M' N' k).

Lemma subst_rec_preserves_l_multi_step : 
forall (red: termred), subst_rec_preserves_l red -> subst_rec_preserves_l (multi_step red). 
Proof. unfold subst_rec_preserves_l. 
 induction 2; split_all.  
apply succ_red with (subst_rec N0 N k); auto.
Qed.

Lemma subst_rec_preserves_r_multi_step : 
forall (red: termred), subst_rec_preserves_r red -> subst_rec_preserves_r (multi_step red). 
Proof. unfold subst_rec_preserves_r. 
 induction 2; split_all.  
apply succ_red with (subst_rec M N k); auto.
Qed.


Lemma subst_rec_preserves_multi_step : 
forall (red: termred), subst_rec_preserves_l red -> subst_rec_preserves_r red -> subst_rec_preserves (multi_step red). 
Proof. 
unfold subst_rec_preserves. split_all.
assert(transitive (multi_step red)) by eapply2 transitive_red. 
unfold transitive in *.
apply X with  (subst_rec M' N k); auto. 
eapply2 subst_rec_preserves_l_multi_step.
eapply2 subst_rec_preserves_r_multi_step.
Qed.



Lemma subst_rec_preserves_l_seq : 
forall red1 , subst_rec_preserves_l red1  -> forall red2 , subst_rec_preserves_l red2  -> 
                                                subst_rec_preserves_l (sequential red1 red2). 
Proof. unfold subst_rec_preserves_l; split_all.  
inversion H1. 
apply seq_red with (subst_rec N0 N k); auto.
Qed.


Lemma subst_rec_preserves_r_seq : 
forall red1 , subst_rec_preserves_r red1  -> forall red2 , subst_rec_preserves_r red2  -> 
                                                         subst_rec_preserves_r (sequential red1 red2). 
Proof. unfold subst_rec_preserves_r; split_all.  
inversion H1. 
apply seq_red with (subst_rec M N0 k); auto.
Qed.


Lemma subst_rec_preserves_seq : 
forall red1 , subst_rec_preserves red1  -> forall red2 , subst_rec_preserves red2  -> 
                                                         subst_rec_preserves (sequential red1 red2). 
Proof. unfold subst_rec_preserves; split_all.  
inversion H1. 
inversion H2. 
apply seq_red with (subst_rec N0 N1 k); auto.
Qed.

Hint Resolve  subst_rec_preserves_multi_step subst_rec_preserves_seq.

Hint Resolve  subst_rec_preserves_multi_step subst_rec_preserves_seq.



Ltac inv red := 
match goal with 
| H: multi_step red (App _ _) _ |- _ => inversion H; clear H; inv red
| H: multi_step red (Ref _) _ |- _ => inversion H; clear H; inv red
| H: multi_step red (Op _) _ |- _ => inversion H; clear H; inv red
| H: multi_step red (Abs _) _ |- _ => inversion H; clear H; inv red
| H: red (Ref _) _ |- _ => inversion H; clear H; inv red
| H: red (App _ _) _ |- _ => inversion H; clear H; inv red
| H: red (Op _) _ |- _ => inversion H; clear H; inv red
| H: red (Abs _) _ |- _ => inversion H; clear H; inv red
| H: multi_step red _ (Ref _) |- _ => inversion H; clear H; inv red
| H: multi_step red _ (App _ _) |- _ => inversion H; clear H; inv red
| H: multi_step red _ (Op _) |- _ => inversion H; clear H; inv red
| H: multi_step red _ (Abs _) |- _ => inversion H; clear H; inv red
| H: red _ (Ref _) |- _ => inversion H; clear H; inv red
| H: red _ (App _ _) |- _ => inversion H; clear H; inv red
| H: red _ (Op _) |- _ => inversion H; clear H; inv red
| H: red _ (Abs _) |- _ => inversion H; clear H; inv red
| |- red (lift _ _) (lift _ _) => unfold lift; eapply2 (lift_rec_preserves red); inv red
| _ => subst; split_all 
 end.


Definition diamond (red1 red2 : termred) := 
forall M N, red1 M N -> forall P, red2 M P -> exists Q, red2 N Q /\ red1 P Q. 

Lemma diamond_flip: forall red1 red2, diamond red1 red2 -> diamond red2 red1. 
Proof. unfold diamond; split_all. elim (H M P H1 N H0); split_all. exist x. Qed.

Lemma diamond_strip : 
forall red1 red2, diamond red1 red2 -> diamond red1 (multi_step red2). 
Proof. intros. 
eapply2 diamond_flip. 
red; induction 1; split_all.
exist P.
elim (H M P0 H2 N); split_all. 
elim(IHmulti_step H x); split_all. 
exist x0.
apply succ_red with x; auto. 
Qed. 


Definition diamond_star (red1 red2: termred) := forall  M N, red1 M N -> forall P, red2 M P -> 
  exists Q, red1 P Q /\ multi_step red2 N Q. 

Lemma diamond_star_strip: forall red1 red2, diamond_star red1 red2 -> diamond (multi_step red2) red1 .
Proof. 
red. induction 2; split_all. 
exist P.
elim(H M P0 H2 N H0); split_all. 
elim(IHmulti_step H x); split_all. 
exist x0.
apply transitive_red with x; auto. 
Qed. 

Lemma diamond_tiling : 
forall red1 red2, diamond red1 red2 -> diamond (multi_step red1) (multi_step red2).
Proof. 
red.  induction 2; split_all.
exist P.
elim(diamond_strip red red2 H M N H0 P0); split_all.
elim(IHmulti_step H x H4); split_all.
exist x0.
apply succ_red with x; auto.
Qed. 

Hint Resolve diamond_tiling. 

Lemma diamond_seq: forall red red1 red2, diamond red red1 -> diamond red red2 -> diamond red (sequential red1 red2). 
Proof. unfold diamond; split_all. 
inversion H2. 
elim(H M N H1 N0); split_all.
elim(H0 N0 x H11 P); split_all.
exist x0. 
apply seq_red with x; auto. 
Qed.

Lemma relocate_null :
forall (n n0 : nat), relocate n n0 0 = n.
Proof. split_all. unfold relocate. case (test n0 n); intro; auto with arith. Qed.

Lemma relocate_lessthan : forall m n k, m<=k -> relocate k m n = (n+k). 
Proof. split_all. unfold relocate. elim(test m k); split_all; try noway. Qed. 
Lemma relocate_greaterthan : forall m n k, m>k -> relocate k m n = k. 
Proof. split_all. unfold relocate. elim(test m k); split_all; try noway. Qed. 

Ltac relocate_lt := 
try (rewrite relocate_lessthan; [| omega]; relocate_lt); 
try (rewrite relocate_greaterthan; [| omega]; relocate_lt);
try(rewrite relocate_null). 


Lemma relocate_zero_succ :
forall n k, relocate 0 (S n) k = 0.
Proof.  split_all. Qed.

Lemma relocate_succ :
forall n n0 k, relocate (S n) (S n0) k = S(relocate n n0 k).
Proof. 
intros; unfold relocate. elim(test(S n0) (S n)); elim(test n0 n); split_all. 
noway. 
noway. 
Qed. 

Lemma relocate_mono : forall M N n k, relocate M n k = relocate N n k -> M=N. 
Proof. 
intros M N n k. 
unfold relocate.
elim(test n M); elim(test n N); split_all; omega. 
Qed. 

Lemma lift_rec_mono : forall M N n k, lift_rec M n k = lift_rec N n k -> M=N. 
Proof. 
induction M; split_all.  
gen_case_inv H N. 
assert(n=n1) by eapply2 relocate_mono. 
subst; auto. 
gen_case_inv H N. 
gen_case_inv H N. 
assert(M = l) by eapply2 IHM. 
congruence. 
gen_case_inv H N. 
assert(M1 = l) by eapply2 IHM1. 
assert(M2 = l0) by eapply2 IHM2. congruence. 
Qed. 



Lemma insert_Ref_lt : forall M n k, n< k -> insert_Ref M n k = Ref n.
Proof.
induction M; unfold insert_Ref; split_all. 
elim (compare k n0); split_all. 
elim a; split_all; try noway. 
elim (compare k n); split_all. 
elim a; split_all; try noway. 
elim (compare k n); split_all. 
elim a; split_all; try noway. 
elim (compare k n); split_all. 
elim a; split_all; try noway. 
Qed. 

Lemma insert_Ref_eq : forall M n k, n= k -> insert_Ref M n k = lift k M.
Proof.
induction M; unfold insert_Ref; split_all. 
elim (compare k n0); split_all. 
elim a; split_all; try noway. 
unfold lift; unfold lift_rec. unfold relocate. elim(test 0 n); split_all; try noway. 
elim (compare k n); split_all. 
elim a; split_all; try noway. 
unfold lift; unfold lift_rec. unfold relocate. elim(test 0 n); split_all; try noway. 
elim (compare k n); split_all. 
elim a; split_all; try noway. 
noway. 
elim (compare k n); split_all. 
elim a; split_all; try noway. 
noway. 
Qed. 


Lemma insert_Ref_gt : forall M n k, n> k -> insert_Ref M n k = Ref (pred n).
Proof.
induction M; unfold insert_Ref; split_all. 
elim (compare k n0); split_all. 
elim a; split_all; try noway. 
noway. 
elim (compare k n); split_all. 
elim a; split_all; try noway. 
noway. 
elim (compare k n); split_all. 
elim a; split_all; try noway. 
noway. 
elim (compare k n); split_all. 
elim a; split_all; try noway. 
noway.
Qed. 

Ltac insert_Ref_out := 
try (rewrite insert_Ref_lt; [|unfold relocate; split_all; omega]; insert_Ref_out); 
try (rewrite insert_Ref_eq; [|unfold relocate; split_all; omega]; insert_Ref_out); 
try (rewrite insert_Ref_gt; [|unfold relocate; split_all; omega]; insert_Ref_out); 
unfold lift; unfold lift_rec; fold lift_rec. 



(* status *) 


Fixpoint status (M: lamSF) := 
match M with 
| Ref i => S i 
| Op _ => 0 
| Abs M1 => pred (status M1) 
| App (Op _) _ => 0 
| App (Abs _) _ => 0 
| App (App (Op _) _) _ => 0 
| App (App (App (Op Sop) _) _) _ => 0 
| App (App (App (Op Fop) M1) _) _ => status M1
| App M1 M2 => status M1 
end.




Definition abs_rank := 10. 

Fixpoint rank (M: lamSF) := 
match M with 
| Ref _ => 1
| Op _ => 1
| App M1 M2 => S((rank M1) + (rank M2))
| Abs M1 =>  abs_rank * rank M1
end.

Lemma rank_positive: forall M, rank M > 0. 
Proof. 
induction M; split_all; try omega. 
Qed. 


Lemma lift_rec_preserves_status : 
forall (M: lamSF) (n k: nat), status (lift_rec M n k) = relocate (status M) (S n) k. 
Proof. 
cut(forall p (M: lamSF) (n k: nat), p>= rank M -> status (lift_rec M n k) = relocate (status M) (S n) k). 
split_all. eapply2 H. 
induction p; intro M. split_all. 
assert(rank M > 0) by eapply2 rank_positive. 
noway. 
(* p > 0 *) 
induction M; split_all; try (rewrite relocate_succ; auto); 
try (eapply2 IHM1). 
(* 2 *) 
rewrite IHM. 
unfold relocate. 
elim(test (S(S n)) (status M)); elim(test (S n) (pred(status M))); split_all; try noway. 
omega. 
assert(rank M > 0) by eapply2 rank_positive. 
omega. 
(* 1 *) 
clear IHM2.
gen2_case IHM1 H M1; try (rewrite relocate_succ; auto); try (eapply2 IHM1). 
gen2_case IHM1 H l; try (rewrite relocate_succ; auto); try (eapply2 IHM1). 
gen2_case IHM1 H l1; try (rewrite relocate_succ; auto); try (eapply2 IHM1). 
case o; split_all. 
eapply2 IHp. omega. 
omega. 
Qed. 

Hint Resolve lift_rec_preserves_status. 


Lemma lift_rec_preserves_rank : 
forall (M: lamSF) (n k: nat), rank (lift_rec M n k) = rank M.
Proof. induction M; split_all. Qed. 

Lemma subst_rec_preserves_status: 
forall (M N: lamSF)(k : nat), (status M <= k -> status (subst_rec M N k) = status M). 
Proof. 
cut(forall p (M: lamSF), p>= rank M -> forall (N: lamSF) (k : nat), (status M <= k -> status (subst_rec M N k) = status M)).
split_all. eapply2 H. 
induction p; intro M. split_all. 
assert(rank M > 0) by eapply2 rank_positive. 
noway. 
(* p > 0 *) 
induction M; intros. 
(* 4 *) 
split_all. simpl in *. insert_Ref_out; split_all.
(* 3 *) 
split_all.
(* 2 *) 
split_all.  
rewrite IHM. auto. simpl in *; omega. simpl in *; omega. 
(* 1 *) 
unfold subst_rec; fold subst_rec. 
(* 1 *) 
generalize IHM1 H H0; clear IHM1 H H0; case M1; intros.  
(* 4 *)
unfold subst_rec; fold subst_rec. 
simpl in H0.  
split_all. 
insert_Ref_out; try (split_all; fail). 
(* 3 *) 
split_all.
(* 2 *) 
 insert_Ref_out; split_all. 
(* 1 *) 
unfold subst_rec; fold subst_rec. 
(* 1 *) 
generalize IHM1 H H0; clear IHM1 H H0; case l; intros.  
(* 4 *)
unfold subst_rec; fold subst_rec. 
simpl in H0.
insert_Ref_out; try (split_all; fail). 
(* 3 *) 
split_all.
(* 2 *) 
 insert_Ref_out; split_all. 
(* 1 *) 
unfold subst_rec; fold subst_rec. 
(* 1 *) 
generalize IHM1 H H0; clear IHM1 H H0; case l1; intros.  
(* 4 *)
unfold subst_rec; fold subst_rec. 
simpl in H0.
insert_Ref_out; try (split_all; fail). 
(* 3 *) 
split_all. 
gen3_case IHM1 H H0 o. 
eapply2 IHp. omega. 
(* 2 *) 
split_all.
(* 1 *) 
unfold subst_rec; fold subst_rec. 
(* 1 *) 
assert(status (App (App (App (App l3 l4) l2) l0) M2) = status(App (App (App l3 l4) l2) l0)).
split_all. 
rewrite H1. 
assert(status (App
        (App
           (App (App (subst_rec l3 N k) (subst_rec l4 N k))
              (subst_rec l2 N k)) (subst_rec l0 N k)) 
        (subst_rec M2 N k)) = status  (subst_rec (App (App (App l3 l4) l2) l0) N k))
by split_all. 
rewrite H2. 
eapply2 IHp. 
simpl in *; omega. 
Qed. 

