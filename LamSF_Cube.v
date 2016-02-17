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
(*                        LamSF_Cube.v                                *)
(*                                                                    *)
(* adapted from Cube.v for Lambda Calculus                            *)
(*                                                                    *)
(*                          Barry Jay                                 *)
(*                                                                    *)
(**********************************************************************)

Require Import Arith.
Require Import LamSF_Terms.
Require Import General.
Require Import Beta_Reduction.
Require Import LamSF_Redexes.
Require Import Test.
Require Import LamSF_Substitution.
Require Import LamSF_Residuals.

(*****************)
(* Prism Theorem *)
(*****************)

(* Auxiliary notion : compat 
   Used to generate the right simultaneous induction on U, V and W *)

(* (compat U V W) iff U,V,W are compatible markings, and (sub V U) *)
Inductive compat : redexes -> redexes -> redexes -> Prop :=
  | Compat_Var : forall i, compat (Var i) (Var i) (Var i)
  | Compat_Oper : forall o, compat (Opp o) (Opp o) (Opp o)
  | Compat_Ap1 :
      forall U1 V1 W1 : redexes,
      compat U1 V1 W1 ->
      forall U2 V2 W2 : redexes,
      compat U2 V2 W2 ->
      forall (b : bool), compat (Ap false U1 U2) (Ap false V1 V2) (Ap b W1 W2)
  | Compat_Ap2 :
      forall U1 V1 W1 ,
      compat U1 V1 W1 ->
      forall U2 V2 W2 : redexes,
      compat U2 V2 W2 ->
      forall (b b' : bool),
      compat (Ap true (Fun U1) U2) (Ap b (Fun V1) V2) (Ap b' (Fun W1) W2)
  | Compat_Fun :
      forall U V W, compat U V W -> compat (Fun U) (Fun V) (Fun W)
.

Hint Resolve Compat_Var Compat_Oper Compat_Ap1 Compat_Ap2 Compat_Fun.

Lemma compat_intro :
 forall U W WU : redexes,
 residuals W U WU ->
 forall (V WV : redexes) (R2 : residuals W V WV) (S : sub V U), compat U V W.
Proof.
(* Remark use of name R2 for uniform command below *)
simple induction 1; intros; generalize S; inversion_clear R2; intros;
 inversion_clear S; split_all; eauto.

inversion_clear S0.  eapply2 Compat_Ap1. 
inversion_clear S0.  
inversion_clear S0. eapply2 Compat_Fun.
inversion_clear S0.
inversion_clear H6. gen_inv H4 H8. subst. eapply2 Compat_Ap2. inversion H12; split_all. eapply2 H1.

inversion S0; subst; split_all.
inversion H11; subst. 
inversion H4; subst. 
eapply2 Compat_Ap2. 

inversion H6; subst. 
inversion S0; subst. inversion H12; subst. 
eapply2 Compat_Ap2. 

inversion H6; subst. 
inversion S0; subst. inversion H12; subst. 
eapply2 Compat_Ap2. 
Qed.

Lemma prism0 :
 forall U V W : redexes,
 compat U V W ->
 forall (UV : redexes) (R1 : residuals U V UV) (WU WV : redexes)
   (R2 : residuals W U WU) (R3 : residuals W V WV), 
 residuals WV UV WU.
Proof.
simple induction 1; 
try (intros; inversion_clear R1; inversion_clear R2; inversion_clear R3; eauto; fail). 
intros. 
gen3_case R1 R2 R3 b.

inversion_clear R1; inversion_clear R2; inversion_clear R3; auto.
unfold subst_r. eapply2 residuals_subst_rec.

inversion_clear R1; inversion_clear R2; inversion_clear R3; auto.
inversion_clear H4; inversion_clear H8; auto.
Qed.

(* Remark - It should be possible to get rid of auxiliary compat
   and to combine prism0 with compat_intro in one lemma *)


(*****************************************************************)
(* Theorem prism : (U,V,W:redexes)(sub V U) ->                   *)
(*     (UV:redexes)(residuals U V UV) ->                         *)
(*     (WV:redexes)(residuals W V WV) ->                         *)
(*     (WU:redexes)(residuals W U WU) <-> (residuals WV UV WU).  *)
(*****************************************************************)

Lemma prism1 :
 forall U V W : redexes,
 sub V U ->
 forall UV : redexes,
 residuals U V UV ->
 forall WV : redexes,
 residuals W V WV ->
 forall WU : redexes, residuals W U WU -> residuals WV UV WU.
Proof.
intros; apply prism0 with U V W; auto.
apply compat_intro with WU WV; trivial.
Qed.

(* Converse of prism1 but needs regularity of U *)
Lemma prism2 :
 forall U V W : redexes,
 sub V U ->
 regular U ->
 forall UV : redexes,
 residuals U V UV ->
 forall WV : redexes,
 residuals W V WV ->
 forall WU : redexes, residuals WV UV WU -> residuals W U WU.
Proof.
intros.
elim (residuals_intro W U); trivial.
intros WU' R; elim (residuals_function WV UV WU) with WU'; trivial.
apply prism1 with U V W; trivial.
apply comp_trans with V.
apply residuals_comp with WV; trivial.
apply comp_sym; apply residuals_comp with UV; trivial.
Qed.

Theorem prism :
 forall U V W : redexes,
 sub V U ->
 forall UV : redexes,
 residuals U V UV ->
 forall WV : redexes,
 residuals W V WV ->
 forall WU : redexes, residuals W U WU <-> regular U /\ residuals WV UV WU.
Proof.
intros; unfold iff in |- *; split.
intro; split.
apply residuals_regular with W WU; trivial.
apply prism1 with U V W; trivial.
simple induction 1; intros; apply prism2 with V UV WV; trivial.
Qed.

(**************************************************************************)
(*  Levy's cube lemma :                                                   *)
(*  (U,V,UV,VU:redexes)  (residuals U V UV) -> (residuals V U VU) ->      *)
(*  (W,WU,WV,WUV:redexes)(residuals W U WU) -> (residuals WU VU WUV) ->   *)
(*                       (residuals W V WV) -> (residuals WV UV WUV).     *)
(**************************************************************************)


Lemma cube :
 forall U V UV VU : redexes,
 residuals U V UV ->
 residuals V U VU ->
 forall W WU WV WUV : redexes,
 residuals W U WU ->
 residuals WU VU WUV -> residuals W V WV -> residuals WV UV WUV.
Proof.
intros.
cut (comp U V).
2: apply residuals_comp with UV; trivial.
intro C; elim (union_defined U V C); intros T UVT.
apply prism1 with T V W; trivial.
apply union_r with U; trivial.
apply preservation with U; trivial.
apply prism2 with U VU WU; trivial.
apply union_l with V; trivial.
apply union_preserve_regular with U V; trivial.
apply residuals_regular with V VU; trivial.
apply residuals_regular with U UV; trivial.
apply preservation with V; trivial.
apply union_sym; trivial.
Qed.


(* 3-dimensional paving diagram *)
Lemma paving :
 forall U V W WU WV : redexes,
 residuals W U WU ->
 residuals W V WV ->
 exists UV : redexes,
   (exists VU : redexes,
      (exists WUV : redexes, residuals WU VU WUV /\ residuals WV UV WUV)).
Proof.
intros; elim (residuals_intro U V).
intros UV R1; exists UV.
elim (residuals_intro V U).
intros VU R2; exists VU.
elim (residuals_intro WU VU).
intros WUV R3; exists WUV.
split; trivial.
apply cube with U V VU W WU; trivial.
apply mutual_residuals_comp with U W V; trivial.
apply residuals_preserve_regular with V U; trivial.
apply residuals_regular with U UV; trivial.
apply comp_sym; apply residuals_comp with UV; trivial.
apply residuals_regular with W WU; trivial.
apply comp_trans with W.
apply comp_sym; apply residuals_comp with WU; trivial.
apply residuals_comp with WV; trivial.
apply residuals_regular with W WV; trivial.
Qed.
