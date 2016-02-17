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
(*                    Analysis.v                                      *)
(*                                                                    *)
(*                     Barry Jay                                      *)
(*                                                                    *)
(**********************************************************************)


Require Import Arith.
Require Import Max. 
Require Import Test.
Require Import General. 
Require Import Terms.
Require Import Substitution_term.
Require Import Lambda_tactics.
Require Import Reduction.
Require Import Confluence.
Require Import SF_reduction.
Require Import LamSF_reduction.
Require Import Normal.
Require Import Closed.
Require Import Eval.
Require Import Equal.
Require Import Binding.
Require Import Analysis.

Fixpoint concrete_comb M := match M with 
| App M1 M2 => wait app_tag (wait (concrete_comb M1) (concrete_comb M2))
| _ => wait op_tag M
end. 

Lemma concrete_combinator: 
forall M, normal M -> combinator M -> lamSF_red (App concrete M) (concrete_comb M).
Proof. 
intros M nor; induction nor; split_all. 
inversion H. 
eapply2 concrete_op. 
inversion H. 
assert(maxvar (App M1 M2) = 0) by eapply2 maxvar_combinator. 
assert(status (App M1 M2) <= maxvar (App M1 M2)) by eapply2 status_lt_maxvar. 
noway. 
apply transitive_red with 
(wait app_tag (wait (App concrete M1) (App concrete M2))). 
eapply2 concrete_compound. 
unfold abs_tag; simpl. 
inversion H; discriminate. 
inversion H0. 
unfold wait; repeat (eapply2 preserves_app_lamSF_red). 
Qed. 

Lemma recursion0 : lamSF_red (App concrete (App k_op (Abs (Ref 0)))) 
(wait app_tag (wait (concrete_comb k_op) (wait abs_tag (concrete_comb i_op)))). 
Proof. 
apply transitive_red with (wait app_tag (wait (App concrete k_op) (App concrete (Abs (Ref 0))))).
eapply2 concrete_compound. 
unfold_op; split_all. 
unfold abs_tag; simpl. discriminate. 
unfold wait.
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red. 
unfold_op. 
eapply2 concrete_combinator. 
eapply2 preserves_app_lamSF_red. 
apply transitive_red with (wait abs_tag (App concrete (star (Ref 0)))). 
eapply2 concrete_abs_1.
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red. 
unfold star. 
unfold_op. 
eapply2 concrete_combinator. 
Qed. 



Lemma recursion1 : lamSF_red (App concrete (Abs (Abs (Ref 0)))) (wait abs_tag (wait app_tag (wait (concrete_comb k_op) (wait abs_tag (concrete_comb i_op))))). 
Proof. 
apply transitive_red with (wait abs_tag (App concrete (App k_op (Abs (Ref 0))))). 
eapply2 concrete_abs_0. 
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red. 
eapply2 recursion0. 
Qed. 


Lemma show : rank (wait abs_tag (wait app_tag (wait (concrete_comb k_op) (wait abs_tag (concrete_comb i_op))))) < 600. 
Proof. simpl. Qed. 
