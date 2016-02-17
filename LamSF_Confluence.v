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
(*                Intensional Lambda Calculus                         *)
(*                                                                    *)
(* is implemented in Coq by adapting the implementation of            *) 
(* Lambda Calculus from Project Coq                                   *)
(* 2015                                                               *)
(**********************************************************************)

(**********************************************************************)
(*                        LamSF_Confluence.v                          *)
(*                                                                    *)
(* adapted from Confluence.v for Lambda Calculus                      *)
(*                                                                    *)
(*                          Barry Jay                                 *)
(*                                                                    *)
(**********************************************************************)

Require Import Arith.
Require Import Test.
Require Import General.
Require Import LamSF_Terms.
Require Import LamSF_Tactics.
Require Import Beta_Reduction.
Require Import LamSF_Redexes.
Require Import LamSF_Marks.
Require Import LamSF_Substitution.
Require Import LamSF_Residuals.
Require Import LamSF_Simulation.
Require Import LamSF_Cube. 

(* Confluence *)

Definition confluence (A : Set) (R : A -> A -> Prop) :=
  forall x y : A,
  R x y -> forall z : A, R x z -> exists u : A, R y u /\ R z u.


(***************************************)
(* Parallel moves lemma and confluence *)
(***************************************)

Lemma parallel_moves : confluence lamSF par_red1.
Proof.

red in |- *; intros M N R1 P R2.
elim (simulation M N); trivial with arith.
elim (simulation M P); trivial with arith.
intros V RV U RU.  
elim (paving U V (mark M) (mark N) (mark P)); trivial with arith.
intros UV C1; elim C1.
intros VU C2; elim C2.
intros UVW C3; elim C3; intros P1 P2.
exists (unmark UVW); split.
rewrite (inverse N).
apply completeness with VU; trivial with arith.
rewrite (inverse P).
apply completeness with UV; trivial with arith.


Qed.

Lemma confluence_parallel_reduction : confluence lamSF par_red.
Proof.
red.
eapply2 diamond_tiling.
eapply2 parallel_moves.
Qed.
