(**********************************************************************)
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


(**********************************************************************)
(*               Intensional Lambda Calculus                          *)
(*                                                                    *)
(* is implemented in Coq by adapting the implementation of            *) 
(* Lambda Calculus from Project Coq                                   *) 
(* 2015                                                               *)
(**********************************************************************)

(**********************************************************************)
(*                           Substitution.v                           *)
(*                                                                    *)
(* adapted from Substitution.v for Lambda Calculus                    *)
(*                                                                    *)
(*                          Barry Jay                                 *)
(*                                                                    *)
(**********************************************************************)

Require Import Arith.
Require Import Lambda.Test.
Require Import Lambda.General.
Require Import Lambda.Terms.
Require Import Lambda.Substitution_term.
Require Import Lambda.Redexes.
Require Import Omega.

(****************************)
(*  Substitution of redexes *)
(****************************)

(* Similar to lift_rec of Terms *)



Fixpoint lift_rec_r (L : redexes) : nat -> nat -> redexes :=
  fun k n : nat =>
  match L with
  | Var i => Var (relocate i k n)
  | Ap b M N => Ap b (lift_rec_r M k n) (lift_rec_r N k n)
  | Fun M => Fun (lift_rec_r M (S k) n)
  end.


Definition lift_r (n : nat) (N : redexes) := lift_rec_r N 0 n.


Definition insert_Var (N : redexes) (i k : nat) :=
  match compare k i with
  
     (* k<i *) | inleft (left _) => Var (pred i)
   (* k=i *) | inleft _ => lift_r k N
   (* k>i *) | _ => Var i
  end.

(* Similar to subst_rec of Terms *)

Fixpoint subst_rec_r (L : redexes) : redexes -> nat -> redexes :=
  fun (N : redexes) (k : nat) =>
  match L with
  | Var i => insert_Var N i k
  | Ap b M M' => Ap b (subst_rec_r M N k) (subst_rec_r M' N k)
  | Fun M => Fun (subst_rec_r M N (S k))
  end.

Definition subst_r (N M : redexes) := subst_rec_r M N 0.


(* Lifting lemmas *)

Lemma lift_le :
 forall (n i k : nat), k <= i -> lift_rec_r (Var i) k n = Var (n + i).
Proof.
simpl in |- *; unfold relocate in |- *.
intros; elim (test k i); intro P; trivial with arith.
absurd (k > i); trivial with arith.
apply le_not_gt; trivial with arith.
Qed.

Lemma lift1 :
 forall (U : redexes) (j i k : nat),
 lift_rec_r (lift_rec_r U i j) (j + i) k = lift_rec_r U i (j + k).
Proof.
simple induction U; split_all; try (case b); split_all.
unfold relocate; elim (test i n); split_all.
elim (test (j + i) (j + n)); split_all.
elim plus_permute; elim plus_assoc; trivial with arith.
noway. 
elim (test (j + i) n); simpl in |- *; intros; trivial with arith.
noway.

replace (S(j+i)) with (j+ S i) by omega. 
rewrite H. auto. 
Qed.

Lemma lift_lift_rec :
 forall (U : redexes) (k p n i : nat),
 i <= n ->
 lift_rec_r (lift_rec_r U i p) (p + n) k = lift_rec_r (lift_rec_r U n k) i p.
Proof.
simple induction U; simpl in |- *; intros; try (case b); split_all.
(* Var *) 
unfold relocate in |- *.
elim (test n0 n); elim (test i n); simpl in |- *.
elim (test (p + n0) (p + n)); elim (test i (k + n)); simpl in |- *; intros.
rewrite plus_permute; trivial with arith.
absurd (i > n); auto with arith.
apply gt_le_trans with (k + n); trivial with arith.
absurd (n0 > n); auto with arith.
apply plus_gt_reg_l with p; trivial with arith.
absurd (n0 > n); auto with arith.
apply plus_gt_reg_l with p; trivial with arith.
intros; absurd (i > n); trivial with arith.
apply le_not_gt; apply le_trans with n0; trivial with arith.
intros; elim (test (p + n0) (p + n)); simpl in |- *; intros;
 trivial with arith.
absurd (n0 > n); trivial with arith.
apply le_not_gt; apply (fun p n m : nat => plus_le_reg_l n m p) with p;
 trivial with arith.
intros; elim (test (p + n0) n); simpl in |- *; intros; trivial with arith.
absurd (n0 > n); trivial with arith.
apply le_not_gt; apply le_trans with (p + n0); trivial with arith.
(* Ap *)

rewrite H; trivial with arith.
rewrite H0; trivial with arith.

rewrite H; trivial with arith.
rewrite H0; trivial with arith.

(* Fun *)
replace (S(p + n)) with (p + S n) by omega. 
rewrite H; auto. omega.  
Qed.

Lemma lift_lift :
 forall (U : redexes) (k p n : nat),
 lift_rec_r (lift_r p U) (p + n) k = lift_r p (lift_rec_r U n k).
Proof.
unfold lift_r in |- *; intros; apply lift_lift_rec; trivial with arith.
Qed.

(* 
Lemma liftrecO : forall (U : redexes) (n : nat), lift_rec_r U n 0 = U.
Proof.
simple induction U; split_all; unfold relocate; elim (test n0 n); split_all.
Qed.

Lemma liftO : forall U : redexes, lift_r 0 U = U.
Proof.
unfold lift_r in |- *; intro U; apply liftrecO.
Qed.

*) 

Lemma lift_rec_lift_rec :
 forall (U : redexes) (n p k i : nat),
 k <= i + n ->
 i <= k -> lift_rec_r (lift_rec_r U i n) k p = lift_rec_r U i (p + n).
Proof.
simple induction U; simpl in |- *; intros; split_all.
(* Var *)
unfold relocate in |- *; elim (test i n); intro P.
elim (test k (n0 + n)); intro Q.
rewrite plus_assoc_reverse; trivial with arith.
absurd (k > n0 + n); trivial with arith.
apply le_not_gt; apply le_trans with (i + n0); trivial with arith.
replace (i + n0) with (n0 + i); auto with arith; apply plus_le_compat_l;
 trivial with arith.
elim (test k n); intro Q; trivial with arith.
absurd (i > k).
apply le_not_gt; trivial with arith.
apply gt_le_trans with n; trivial with arith.
(* Ap *)
rewrite H; trivial with arith; rewrite H0; trivial with arith.
(* Fun *)
rewrite H; trivial with arith; try omega.   
Qed.

Lemma lift_rec_lift :
 forall (U : redexes) (n p k i : nat),
 k <= n -> lift_rec_r (lift_r n U) k p = lift_r (p + n) U.
Proof.
unfold lift_r in |- *; intros; rewrite lift_rec_lift_rec; trivial with arith.
Qed.


(* The three cases of substitution of U for (Var n) *)

Lemma subst_eq :
 forall (M U : redexes) (n : nat), 
  subst_rec_r (Var n) U n = lift_r n U.
Proof.
simpl in |- *; unfold insert_Var in |- *.
intros; elim (compare n n); intro P.
elim P; intro Q; simpl in |- *; trivial with arith.
absurd (n > n); trivial with arith.
absurd (n > n); trivial with arith.
Qed.

Lemma subst_gt :
 forall (M U : redexes) (n p : nat),
 n > p -> subst_rec_r (Var n) U p =  Var (pred n).
Proof.
simpl in |- *; unfold insert_Var in |- *.
intros; elim (compare p n); intro P.
elim P; intro Q; trivial with arith.
absurd (n > p); trivial with arith; rewrite Q; trivial with arith.
absurd (n > p); auto with arith.
Qed.


Lemma subst_lt :
 forall (U : redexes) (n p : nat), p > n -> subst_rec_r (Var n) U p = Var n.
Proof.
simpl in |- *; unfold insert_Var in |- *.
intros; elim (compare p n); intro P; trivial with arith.
absurd (p > n); trivial with arith; elim P; intro Q; auto with arith.
rewrite Q; trivial with arith.
Qed.


(* Substitution lemma *)

Lemma lift_rec_subst_rec :
 forall (V U : redexes) (k p n : nat),
 lift_rec_r (subst_rec_r V U p) (p + n) k =
 subst_rec_r (lift_rec_r V (S (p + n)) k) (lift_rec_r U n k) p.
Proof.
simple induction V; split_all.
(* 2 Fun *) 
2: replace (S(p + n)) with (S p +  n) by omega;  rewrite H; auto. 
(* 1 Var *)
unfold insert_Var, relocate in |- *.
elim (compare p n); intro P.
(* 1.1  P : {(gt n p)}+{p=n} *)
elim P; intro P1.
(* 1.1.1 P1 : (gt n p) *)
elim (test (S (p + n0)) n); intro Q.
(* 1.1.1.1 Q : (le (S (plus p n0)) n) *)
elim (compare p (k + n)); intro R.
(* 1.1.1.1.1 R : {(lt p (plus k n))}+{p=(plus k n)} *)
elim R; intro R1; simpl in |- *.
(* 1.1.1.1.1.1 R1 : (lt p (plus k n)) *)
unfold relocate in |- *.
elim (test (p + n0) (pred n)); intro S.
assert(k+ pred n = pred (k+n)) by omega. 
rewrite H; auto. 
noway. 
noway. 
noway. 
elim (compare p n); intro R.
(* 1.1.1.2.1  R : {(lt p n)}+{p=n} *)
elim R; intro R1.
simpl. 
unfold relocate. 
(* 1.1.1.2.1.1  R1 : (lt p n) *)
elim (test (p + n0) (pred n)); intro C.
noway. 
auto. 
noway. 
noway. 
elim (test (S (p + n0)) n); intro Q.
(* 1.1.2.1  Q : (le (S (plus n n0)) n) *)
noway. 
subst. 
(* 1.1.2.2  Q : (gt (S (plus n n0)) n) *)
elim (compare n n); intro R.
(* 1.1.2.2.1  R : {(lt n n)}+{n=n} *)
elim R; intro R1. 
noway. 
rewrite lift_lift; trivial with arith.
noway. 
(* 1.2  P : (gt p n) *)
elim (test (S (p + n0)) n); intro Q.
(* 1.2.1  Q : (le (S (plus p n0)) n) *)
noway. 
elim (compare p n); intro R.
(* 1.2.2.1  R : {(lt p n)}+{p=n} *)
elim R; intro R1; try noway. 
simpl. 
unfold relocate. 
elim(test (p+n0) n); split_all; try noway. 
Qed. 

Lemma lift_subst :
 forall (U V : redexes) (k n : nat),
 lift_rec_r (subst_r U V) n k =
 subst_r (lift_rec_r U n k) (lift_rec_r V (S n) k).
Proof.
unfold subst_r in |- *; intros.
replace (S n) with (S (0 + n)).
elim lift_rec_subst_rec; trivial with arith.
simpl in |- *; trivial with arith.
Qed.


Lemma subst_rec_lift_rec1 :
 forall (U V : redexes) (n p k : nat),
 k <= n ->
 subst_rec_r (lift_rec_r U k p) V (p + n) =
 lift_rec_r (subst_rec_r U V n) k p.
Proof.
simple induction U; intros; simpl in |- *; split_all.
(* Var *)
unfold relocate. 
elim(test k n); split_all; try noway.  
unfold insert_Var. 
elim(compare (p+n0) (p+n)); elim(compare n0 n); split_all; try noway. 
elim a1; split_all; try noway. 
elim a0; split_all; try noway. 
unfold relocate. 
elim(test k (pred n)); split_all; try noway. 
assert(pred (p+n) = p + pred n) by omega. 
rewrite H0; split_all. 
elim a0; split_all; try noway. 
rewrite lift_rec_lift; split_all. 
elim a0; split_all; try noway. 
elim a0; split_all; try noway. 
unfold relocate. 
elim(test k n); split_all; try noway. 

unfold insert_Var. 
elim(compare n0 n); split_all; try noway. 
elim a; split_all; try noway. 
elim(compare (p+n0) n); split_all; try noway. 
elim a; split_all; try noway. 
unfold relocate. 
elim(test k n); split_all; try noway. 

rewrite H; split_all. rewrite H0; split_all. 

replace (S(p + n)) with (p + (S n)) by omega. 
rewrite H; auto; try omega. 
Qed. 


Lemma subst_rec_lift1 :
 forall (U V : redexes) (n p : nat),
 subst_rec_r (lift_r p U) V (p + n) = lift_r p (subst_rec_r U V n).
Proof.
unfold lift_r in |- *; intros; rewrite subst_rec_lift_rec1;
 trivial with arith.
Qed.


Lemma subst_rec_lift_rec :
 forall (U V : redexes) (p q n : nat),
 q <= p + n ->
 n <= q -> subst_rec_r (lift_rec_r U n (S p)) V q = lift_rec_r U n p.
Proof.
simple induction U; intros; simpl in |- *; try (case b); split_all.


unfold insert_Var, relocate in |- *; simpl in |- *.
elim (test n0 n); intro P.
(* 1  P : (le n0 n) *)
elim (compare q (S (p + n))); intro Q; try noway.
(* 1.1  Q : {(lt q (S (plus p n)))}+{q=(S (plus p n))} *)
elim Q; intro Q1; simpl in |- *; trivial with arith; try noway. 
elim (compare q n); intro Q; trivial with arith; try noway.
(* 2.1 Q : {(lt n q)}+{q=n} *)
elim Q; intro Q1; simpl in |- *; trivial with arith; try noway. 
rewrite H; split_all. 
rewrite H0; split_all. 

rewrite H; split_all. 
rewrite H0; split_all. 

rewrite H; split_all; try omega.  
Qed. 

Lemma subst_rec_lift :
 forall (U V : redexes) (p q : nat),
 q <= p -> subst_rec_r (lift_r (S p) U) V q = lift_r p U.
Proof.
unfold lift_r in |- *; intros; rewrite subst_rec_lift_rec; trivial with arith.
elim plus_n_O; trivial with arith.
Qed.

(* subst_rec_subst_rec *)

Lemma subst_rec_subst_rec :
 forall (V U W : redexes) (n p : nat),
 subst_rec_r (subst_rec_r V U p) W (p + n) =
 subst_rec_r (subst_rec_r V W (S (p + n))) (subst_rec_r U W n) p.
Proof.
simple induction V; split_all.
2: replace (S(p+n)) with (S p+n) by omega; rewrite H; split_all.

unfold insert_Var in |- *.
elim (compare p n); intro C.
(* 1.1  C : {(lt p n)}+{p=n} *)
elim C; intro D.
(* 1.1.1  D : (lt p n) *) 
elim (compare (S (p + n0)) n); intro P; try noway. 
(* 1.1.1.1  P : {(lt (S (plus p i)) n)}+{(S (plus p i))=n} *)
elim P; intro P1; try noway. 
simpl. 
unfold insert_Var.  
elim(compare (p+n0) (pred n)); split_all. 
elim a; split_all; try noway.  
elim(compare p (pred n)); split_all; try noway. 
elim a1; split_all; try noway.  
elim(compare p (pred n)); split_all; try noway. 

simpl.  
unfold insert_Var.  
elim(compare (p+n0) (pred n)); split_all. 
elim a; split_all; try noway.  
rewrite subst_rec_lift. auto. 
omega. 
noway. 

simpl. 
unfold insert_Var.  
elim(compare (p+n0) (pred n)); split_all. 
elim a; split_all; try noway.  
elim(compare p n); split_all; try noway. 
elim a; split_all; try noway.  

elim(compare (S(p+n0)) n); split_all; try noway. 
elim a; split_all; try noway. 
unfold insert_Var.  
elim(compare p n); split_all. 
elim a; split_all; try noway.  
rewrite subst_rec_lift1. auto. 
noway. 

elim(compare (S (p + n0)) n); split_all; try noway. 
elim a; split_all; try noway.  
unfold insert_Var.  
elim(compare (p+n0) n); split_all; try noway. 
elim a; split_all; try noway.  
elim(compare p n); split_all; try noway. 
elim a; split_all; try noway.  
Qed. 

Lemma subst_rec_subst_0 :
 forall (U V W : redexes) (n : nat),
 subst_rec_r (subst_rec_r V U 0) W n =
 subst_rec_r (subst_rec_r V W (S n)) (subst_rec_r U W n) 0.
Proof.
intros; pattern n at 1 3 in |- *.
replace n with (0 + n).
rewrite (subst_rec_subst_rec V U W n 0); trivial with arith.
simpl in |- *; trivial with arith.
Qed.

(**************************)
(* The Substitution Lemma *)
(**************************)

Lemma substitution :
 forall (U V W : redexes) (n : nat),
 subst_rec_r (subst_r U V) W n =
 subst_r (subst_rec_r U W n) (subst_rec_r V W (S n)).
Proof.
unfold subst_r in |- *; intros; apply subst_rec_subst_0; trivial with arith.
Qed.

(* Substitution preserves compatibility *)

Lemma lift_rec_preserve_comp :
 forall U1 V1 : redexes,
 comp U1 V1 -> forall n m : nat, comp (lift_rec_r U1 m n) (lift_rec_r V1 m n).
Proof. simple induction 1; simpl in |- *; intro b; case b; split_all. Qed.

Lemma subst_rec_preserve_comp :
 forall U1 V1 : redexes, comp U1 V1 ->
 forall U2 V2,  comp U2 V2 ->
 forall n : nat, comp (subst_rec_r U1 U2 n) (subst_rec_r V1 V2 n).
Proof.
simple induction 1; simpl in |- *; auto with arith.
split_all; unfold insert_Var.
 elim (compare n i); split_all. 
elim a; split_all. 
unfold lift_r. 
eapply2 lift_rec_preserve_comp.
Qed.

Lemma subst_preserve_comp :
 forall U1 V1 U2 V2 : redexes,
 comp U1 V1 -> comp U2 V2 -> comp (subst_r U2 U1) (subst_r V2 V1).
Proof.
intros; unfold subst_r in |- *; apply subst_rec_preserve_comp;
 trivial with arith.
Qed.

(* Substitution preserves regularity *)

Lemma lift_rec_preserve_regular :
 forall U : redexes,
 regular U -> forall n m : nat, regular (lift_rec_r U m n).
Proof.
simple induction U; simpl in |- *; auto with arith; split_all.
gen2_case H H1 b. 
gen2_case H H1 r.
Qed.


Lemma subst_rec_preserve_regular :
 forall U V : redexes,
 regular U -> regular V -> forall n : nat, regular (subst_rec_r U V n).
Proof.
intro U; elim U; simpl in |- *; auto with arith; split_all.
unfold insert_Var in |- *; elim (compare n0 n); split_all. 
elim a; split_all. 
unfold lift_r in |- *; apply lift_rec_preserve_regular;
 trivial with arith.
gen_case H1 b. 
gen2_case H H1 r. 
Qed.

Lemma subst_preserve_regular :
 forall U V : redexes, regular U -> regular V -> regular (subst_r U V).
Proof.
unfold subst_r in |- *; intros; apply subst_rec_preserve_regular;
 trivial with arith.
Qed.