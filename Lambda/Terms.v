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
(*                           Terms.v                                  *)
(*                                                                    *)
(* adapted from Terms.v for Lambda Calculus                           *)
(*                                                                    *)
(*                          Barry Jay                                 *)
(*                                                                    *)
(**********************************************************************)



Require Import Arith.
Require Import Lambda.General.
Require Import Lambda.Test.


(* lambda terms using de Bruijn's indices *)


Inductive lambda:  Set :=
  | Ref : nat -> lambda 
  | Abs : lambda -> lambda  
  | App : lambda -> lambda -> lambda
.

Lemma decidable_term_equality : forall (M N: lambda), M = N \/ M<> N. 
Proof. 
induction M; induction N; intros; try (left; congruence); try(right; congruence). 
elim(decidable_nats n0 n); auto. 
intro; right; intro; congruence. 
elim(IHM N); split_all.
left; congruence.
right; congruence. 
elim(IHM1 N1); elim(IHM2 N2); auto; 
(right; congruence; fail) || left; congruence. 
Qed. 


(* Lifting *)

Definition relocate (i k n : nat) :=
  match test k i with
  
      (* k<=i *) | left _ => n+i
   (* k>i  *) | _ => i
  end.

Fixpoint lift_rec (L : lambda) : nat -> nat -> lambda :=
  fun k n => 
  match L with
  | Ref i => Ref (relocate i k n)
  | App M N => App (lift_rec M k n) (lift_rec N k n)
  | Abs M => Abs (lift_rec M (S k) n)
  end.

Definition lift (n : nat) (N : lambda) := lift_rec N 0 n.

(* Substitution *)


Definition insert_Ref (N : lambda) (i k : nat) :=
  match compare k i with
  
   (* k<i *) | inleft (left _) => Ref (pred i)
   (* k=i *) | inleft _ => lift k N
   (* k>i *) | _ => Ref i
  end.

Fixpoint subst_rec (L : lambda) : lambda -> nat -> lambda :=
  fun (N : lambda) (k : nat) =>
  match L with
  | Ref i => insert_Ref N i k
  | App M M' => App (subst_rec M N k) (subst_rec M' N k)
  | Abs M => Abs (subst_rec M N (S k)) 
  end.

Definition subst (N M : lambda) := subst_rec M N 0.


