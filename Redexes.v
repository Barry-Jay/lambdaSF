(* This prqogram is free software; you can redistribute it and/or      *)
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
(*                           Redexes.v                                *)
(*                                                                    *)
(* adapted from Redexes.v for Lambda Calculus                         *)
(*                                                                    *)
(*                          Barry Jay                                 *)
(*                                                                    *)
(**********************************************************************)

Require Import Arith.
Require Import General.
Require Import Test.
Require Import Terms.

(*****************************)
(* Terms with marked redexes *)
(*****************************)

Inductive redexes : Set :=
  | Var : nat -> redexes 
  | Opp : operator -> redexes
  | Ap : bool -> redexes -> redexes -> redexes
  | Fun : redexes -> redexes
.

(* A redex is marked as (Ap true (Fun false M) N) *)

(* The Boolean algebra of sets of redexes *)

Inductive sub : redexes -> redexes -> Prop := 
  | Sub_Var : forall i : nat, sub (Var i) (Var i)
  | Sub_Oper : forall o, sub (Opp o) (Opp o)
  | Sub_Ap1 :
      forall U1 V1 : redexes,
      sub U1 V1 ->
      forall U2 V2 : redexes, 
      sub U2 V2 -> forall (b : bool), sub (Ap false U1 U2) (Ap b V1 V2)
  | Sub_Ap2 :
      forall U1 V1 : redexes,
      sub U1 V1 ->
      forall U2 V2 : redexes,
      sub U2 V2 -> forall (b : bool), sub (Ap true U1 U2) (Ap true V1 V2)
 | Sub_Fun : forall U V , sub U V -> sub (Fun U) (Fun V)
.

Hint Resolve Sub_Var Sub_Oper Sub_Fun Sub_Ap1 Sub_Ap2.


Definition bool_max (b b' : bool) :=
  match b return bool with
  | true => true
  | false => b'
  end.

Lemma max_false : forall b : bool, bool_max b false = b.
Proof.
simple induction b; simpl in |- *; trivial.
Qed.

Inductive union : redexes -> redexes -> redexes -> Prop :=
  | Union_Var : forall i: nat, union (Var i) (Var i) (Var i)
  | Union_Oper : forall o, union (Opp o) (Opp o) (Opp o)
  | Union_Ap :
      forall U1 V1 W1 : redexes,
      union U1 V1 W1 ->
      forall U2 V2 W2 : redexes,
      union U2 V2 W2 ->
      forall (b1 b2 : bool),
      union (Ap b1 U1 U2) (Ap b2 V1 V2) (Ap (bool_max b1 b2) W1 W2)
  | Union_Fun : forall U V W, union U V W -> union (Fun U) (Fun V) (Fun W)
.

Hint Resolve Union_Var Union_Oper Union_Fun Union_Ap.

Lemma union_l : forall U V W : redexes, union U V W -> sub U W.
Proof.
simple induction 1; split_all. 
elim b1.
elim b2; simpl in |- *; apply Sub_Ap2; trivial.
elim b2; simpl in |- *; apply Sub_Ap1; trivial.
Qed.

Lemma union_r : forall U V W : redexes, union U V W -> sub V W.
Proof.
simple induction 1; split_all. 
elim b2.
elim b1; simpl in |- *; apply Sub_Ap2; trivial.
elim b1; simpl in |- *; apply Sub_Ap1; trivial.
Qed.

Lemma bool_max_Sym : forall b b' : bool, bool_max b b' = bool_max b' b.
Proof.
simple induction b; simple induction b'; simpl in |- *; trivial.
Qed.

Lemma union_sym : forall U V W : redexes, union U V W -> union V U W.
Proof.
simple induction 1; split_all.
rewrite (bool_max_Sym b1 b2); split_all.
Qed.

(* Compatibility *)
(* (comp U V) iff (unmark U)=(unmark V) *)

Inductive comp : redexes -> redexes -> Prop :=
  | Comp_Var : forall i: nat, comp (Var i) (Var i)
  | Comp_Oper : forall o, comp (Opp o) (Opp o) 
  | Comp_Ap :
      forall U1 V1 : redexes,
      comp U1 V1 ->
      forall U2 V2 : redexes,
      comp U2 V2 -> forall (b1 b2 : bool), comp (Ap b1 U1 U2) (Ap b2 V1 V2)
  | Comp_Fun : forall U V, comp U V -> comp (Fun U) (Fun V)
.
Hint Resolve Comp_Var Comp_Oper Comp_Fun Comp_Ap.

Lemma comp_refl : forall U : redexes, comp U U.
Proof.
simple induction U; auto.
Qed.

Lemma comp_sym : forall U V : redexes, comp U V -> comp V U.
Proof.
simple induction 1; auto.
Qed.

Lemma comp_trans :
 forall U V : redexes,
 comp U V -> forall (W : redexes) (CVW : comp V W), comp U W.
simple induction 1; intros; inversion_clear CVW; auto.
Qed.


Lemma union_defined :
 forall U V : redexes, comp U V -> exists W : redexes, union U V W.
Proof. simple induction 1; split_all; eauto. Qed.


(* A element of type redexes is said to be regular if its true marks label
   redexes *)


Fixpoint regular (U : redexes) : Prop :=
  match U with
  | Var _ => True
  | Opp _ => True
  | Ap true (Fun _ as V) W => regular V /\ regular W
  | Ap true _ W => False
  | Ap false V W => regular V /\ regular W
  | Fun V => regular V
  end.

Lemma union_preserve_regular :
 forall U V W : redexes, union U V W -> regular U -> regular V -> regular W.
Proof.
simple induction 1; split_all. 
gen_case H4 b1. 
gen_case H5 b2.
gen3_case H0 H1 H4 U1. 
gen3_case H0 H1 H5 V1. 
inversion H0; split_all; subst.  
simpl in *. 
eapply2 H1. 

gen3_case H0 H1 H4 U1. 
inversion H0. subst; split_all. 

gen_case H5 b2.
gen3_case H0 H1 H5 V1. 
inversion H0. subst; split_all. 
Qed.





