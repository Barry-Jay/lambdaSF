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
(*                 Intensional Lambda Calculus                        *)
(*                                                                    *)
(* is implemented in Coq by adapting the implementation of            *) 
(* Lambda Calculus from Project Coq                                   *)
(* 2015                                                               *)
(**********************************************************************)

(**********************************************************************)
(*                        LamSF_Residuals.v                           *)
(*                                                                    *)
(* adapted from Residuals.v for Lambda Calculus                       *)
(*                                                                    *)
(*                          Barry Jay                                 *)
(*                                                                    *)
(**********************************************************************)

Require Import Arith.
Require Import Test.
Require Import General.
Require Import LamSF_Terms.
Require Import LamSF_Substitution.
Require Import LamSF_Redexes.
Require Import Omega.


(*************************************************)
(* Parallel beta reduction with residual tracing *)
(*************************************************)

(* (residuals U V W) means W are residuals of redexes U by step V *)

Inductive residuals : redexes -> redexes -> redexes -> Prop :=
  | Res_Oper : forall o, residuals (Opp o) (Opp o) (Opp o)
  | Res_Var : forall i, residuals (Var i) (Var i) (Var i)
  | Res_Ap :
      forall U1 V1 W1 : redexes,
      residuals U1 V1 W1 ->
      forall U2 V2 W2 : redexes,
      residuals U2 V2 W2 ->
      forall (b : bool), residuals (Ap b U1 U2) (Ap false V1 V2) (Ap b W1 W2)
   | Res_Fun :
      forall U V W ,
      residuals U V W -> residuals (Fun U) (Fun V) (Fun W)
  | Res_redex :
      forall U1 V1 W1 : redexes,
      residuals U1 V1 W1 ->
      forall U2 V2 W2 : redexes,
      residuals U2 V2 W2 ->
      forall (b : bool),
      residuals (Ap b (Fun U1) U2) (Ap true (Fun V1) V2) (subst_r W2 W1)
.

Hint Resolve Res_Var Res_Oper Res_Fun Res_Ap Res_redex.

Lemma residuals_function :
 forall U V W : redexes,
 residuals U V W -> forall (W' : redexes) (R : residuals U V W'), W' = W.
Proof.
(* Remark use of name R necessary for uniform expression of next line *)
simple induction 1; intros; inversion R; auto with arith.
elim H1 with W0; elim H3 with W3; trivial with arith.
elim H1 with W1; trivial with arith.
elim H1 with W0; elim H3 with W3; trivial with arith.
Qed.

(* Commutation theorem *)

Lemma residuals_lift_rec :
 forall U1 U2 U3 : redexes,
 residuals U1 U2 U3 ->
 forall k n : nat,
 residuals (lift_rec_r U1 n k) (lift_rec_r U2 n k) (lift_rec_r U3 n k).
Proof.
simple induction 1; simpl in |- *; intros; auto with arith; split_all.
assert(n = 0+n) by omega. rewrite H4 at 5.  
unfold subst_r.  rewrite lift_rec_subst_rec. 
eapply2 Res_redex.
Qed.

Lemma residuals_lift :
 forall U1 U2 U3 : redexes,
 residuals U1 U2 U3 ->
 forall k : nat, residuals (lift_r k U1) (lift_r k U2) (lift_r k U3).
Proof.
unfold lift_r in |- *; intros; apply residuals_lift_rec; trivial with arith.
Qed.
Hint Resolve residuals_lift.

Lemma residuals_subst_rec :
 forall U1 U2 U3 : redexes,
 residuals U1 U2 U3 -> forall V1 V2 V3, 
 residuals V1 V2 V3 ->
 forall k : nat,
 residuals (subst_rec_r U1 V1 k) (subst_rec_r U2 V2 k) (subst_rec_r U3 V3 k).
Proof.
simple induction 1; simpl in |- *; auto with arith; split_all.
 unfold insert_Var in |- *; elim (compare k i); auto with arith.
simple induction a; auto with arith.
unfold subst_r. 
assert(k = 0+k) by omega. rewrite H5. 
rewrite subst_rec_subst_rec; auto with arith.
eapply2 Res_redex.
Qed.
Hint Resolve residuals_subst_rec.

(***************************)
(* The Commutation Theorem *)
(***************************)

Theorem commutation :
 forall U1 U2 U3 V1 V2 V3 : redexes,
 residuals U1 U2 U3 ->
 residuals V1 V2 V3 ->
 residuals (subst_r V1 U1) (subst_r V2 U2) (subst_r V3 U3).
Proof.
unfold subst_r in |- *; auto with arith.
Qed.

Lemma residuals_comp : forall U V W : redexes, residuals U V W -> comp U V.
Proof.
simple induction 1; simpl in |- *; auto with arith.
Qed.

Lemma preservation1 :
 forall U V UV : redexes,
 residuals U V UV ->
 forall (T : redexes) (UVT : union U V T), residuals T V UV.
Proof.
(* Remark use of name UVT for uniform command below *)
simple induction 1; simple induction T; intros; inversion UVT;
 auto with arith.
rewrite (max_false b); auto with arith.
inversion H8; auto with arith.
Qed.

Lemma preservation :
 forall U V W UV : redexes,
 union U V W -> residuals U V UV -> residuals W V UV.
Proof.
intros; apply preservation1 with U; auto with arith.
Qed.

Lemma mutual_residuals_comp :
 forall (W U UW : redexes) (RU : residuals U W UW) 
   (V VW : redexes) (RV : residuals V W VW), comp UW VW.
Proof.
simple induction W; split_all.
inversion_clear RU; inversion_clear RV; trivial with arith.
inversion_clear RU; inversion_clear RV; trivial with arith.
2: inversion_clear RU; inversion_clear RV; trivial with arith;
 eapply2 Comp_Fun.
induction b; split_all. 
2: inversion_clear RU; inversion_clear RV;
apply Comp_Ap;[ eapply2 H| eapply2 H0]. 

inversion RU; inversion RV; subst. invsub.
apply subst_preserve_comp.
assert(residuals (Fun U1) (Fun V1) (Fun W1)). eapply2 Res_Fun. 
assert(residuals (Fun U0) (Fun V1) (Fun W0)). eapply2 Res_Fun.
assert(comp (Fun W1) (Fun W0)) by 
eapply2 (H (Fun U1) (Fun W1) H1 (Fun U0) (Fun W0) H2).
inversion H3. subst. auto. 
eapply2 H0. 
Qed. 


(* We take residuals only by regular redexes *)

Lemma residuals_regular :
 forall U V W : redexes, residuals U V W -> regular V.
Proof.
simple induction 1; simpl in |- *; auto with arith.
Qed.

(* Conversely, residuals by compatible regular redexes always exist 
   (and are unique by residuals_function lemma above) *)

Lemma residuals_intro :
 forall U V : redexes,
 comp U V -> regular V -> exists W : redexes, residuals U V W.
Proof.
simple induction 1; simpl in |- *; split_all; eauto.
2: elim H1; split_all; eauto.
gen_case H4 b2.
2: elim H1; elim H3; split_all; exist (Ap b1 x0 x).
gen2_case H1 H4 V1. 
elim H1; elim H3; split_all. 
inversion H7; subst. 
inversion H0. subst. 
exist (subst_r x W). 
Qed.

(* Residuals preserve regularity *)

Lemma residuals_preserve_regular :
 forall U V W : redexes, residuals U V W -> regular U -> regular W.
Proof.
simple induction 1; simpl in |- *; auto with arith.     
simple induction b.
split_all. 
gen3_case H1 H0 H4 U1.
gen2_case H0 H1 W1; inversion H0. 
split_all. 
split_all. 
split_all. 
split_all. 
gen_case H4 b; 
eapply2 subst_rec_preserve_regular.
Qed.
