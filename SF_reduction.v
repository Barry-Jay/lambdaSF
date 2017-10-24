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
(*                   SF_reduction.v                                   *)
(*                                                                    *)
(*                     Barry Jay                                      *)
(*                                                                    *)
(**********************************************************************)

Require Import Arith.
Require Import Test. 
Require Import General.
Require Import LamSF_Terms. 
Require Import LamSF_Tactics.
Require Import LamSF_Substitution_term. 
Require Import Beta_Reduction.
Require Import LamSF_Confluence. 
Require Import Omega.


Definition s_op := Op Sop.
Definition f_op := Op Fop.
Definition k_op := App f_op f_op. 
Definition i_op := App (App s_op k_op) k_op.
Definition abs_left := App (App s_op k_op) f_op.
Ltac unfold_op := unfold abs_left, i_op, id, k_op, f_op, s_op. 


(* components *) 

 
Fixpoint star M := 
match M with 
| Ref 0 => i_op 
| Ref (S n) => App k_op (Ref n)
| Op o => App k_op (Op o)
| Abs M1 =>  Abs (star M1)
| App M1 M2 => App (App s_op (Abs M1)) (Abs M2)
end
.



Lemma rank_star: 
forall M, rank (star M) < rank (Abs M). 
Proof. 
induction M; intros. 
(* 4 *) 
case n; split_all; omega. 
(* 3 *) 
split_all; omega. 
(* 2 *)
unfold star, rank; fold rank; fold star. 
eapply2 times_monotonic2. 
unfold abs_rank; omega. 
eapply2 rank_positive. 
(* 1 *) 
unfold star; fold star. 
unfold_op; unfold rank; fold rank. 
replace(abs_rank * S (rank M1 + rank M2)) with (abs_rank + abs_rank * (rank M1) + abs_rank * (rank M2)). 
2: split_all; omega. 
assert(3 < abs_rank) by (unfold abs_rank; omega). 
omega. 
Qed. 


Lemma star_monotonic: 
forall M N, 
star M = star N -> M = N. 
Proof. 
induction M; split_all. 
(* 4 *) 
gen_case H n. 
(* 5 *) 
gen_case H N; try discriminate. 
(* 5 *) 
gen_case H n0; discriminate.
(* 4 *) 
gen_case H N. 
gen_case H n1. 
discriminate. 
(* 3 *) 
gen_case H N. 
gen_case H n.
discriminate. 
(* 2 *) 
gen_case H N. 
gen_case H n.
discriminate. 
inversion H. 
assert(M = l). eapply2 IHM. 
congruence. 
(* 1 *) 
gen_case H N. 
gen_case H n.
discriminate. 
Qed. 

Fixpoint right_component (M : lamSF) := 
match M with 
| App _ M2 => M2
| Abs M1 => star M1
| _ => M
end.

Definition left_component (U : lamSF) := 
match U with 
| App U1 _ => U1 
| _ => abs_left 
end.


Lemma rank_component_app_l: 
forall M N, rank (left_component (App M N)) < rank (App M N). 
Proof. split_all; omega. Qed. 

Lemma rank_component_app_r: 
forall M N, rank (right_component (App M N)) < rank (App M N). 
Proof. split_all; omega. Qed. 

Lemma rank_component_abs_l: 
forall M, rank (left_component (Abs M)) < rank (Abs M). 
Proof. 
induction M; intros. 
split_all; try omega. 
split_all; try omega. 
assert(rank M >0) by eapply2 rank_positive. 
unfold left_component. unfold_op; unfold rank; fold rank. 
replace (abs_rank * (abs_rank * rank M)) with (abs_rank * abs_rank * rank M) by ring. 
cut (S (S (1 + S (1 + 1)) + S (1 + 1)) < abs_rank * abs_rank). 
2: unfold abs_rank; split_all; omega. intro. 
replace (rank M) with (1+ (pred (rank M))) by omega. 
replace(abs_rank * abs_rank * (1+ (pred (rank M)))) with
(abs_rank * abs_rank + abs_rank * abs_rank * (pred (rank M))) by ring. 
assert(0 <= abs_rank * abs_rank * pred (rank M)). 
case (abs_rank * abs_rank * pred (rank M)); split_all. 
omega. 
omega. 
(* 1 *) 
unfold left_component; unfold_op. unfold rank; fold rank. 
assert(S (S (1 + S (1 + 1)) + S (1 + 1)) < abs_rank). 
unfold abs_rank; split_all; omega. 
split_all; omega.  
Qed. 


Lemma rank_component_abs_r: 
forall M, rank (right_component (Abs M)) < rank (Abs M). 
Proof. 
unfold right_component.  intros. eapply2 rank_star. 
Qed. 


Lemma lift_rec_preserves_star : forall (M : lamSF) n k, 
  lift_rec(star M) n k = star (lift_rec M (S n) k).
Proof. 
induction M; split_all. 
 case n; split_all. 
rewrite relocate_succ. auto.
Qed. 


Lemma  lift_rec_preserves_components_l : forall (M : lamSF) n k, 
  lift_rec(left_component M) n k = left_component(lift_rec M n k).
Proof. induction M; split_all; case b0; case b; split_all. Qed. 

Lemma  lift_rec_preserves_components_r : forall (M : lamSF) n k, 
  lift_rec(right_component M) n k = right_component(lift_rec M n k).
Proof. induction M; split_all. 
rewrite lift_rec_preserves_star.  
auto. 
Qed. 


Lemma star_preserves_status : 
forall M, (status (star M) = pred(status M) \/ status(star M) = 0) .
Proof. 
induction M; split_all. case n; split_all. inversion IHM.  left; omega. right; omega. 
Qed.



(* compounds *) 


Inductive compound : lamSF -> Prop := 
| op1_compound : forall M o, compound (App (Op o) M)
| op2_compound : forall M N o, compound (App (App (Op o) M) N)
| abs_op_compound : forall o, compound (Abs (Op o))
| abs_compound_compound : forall M, compound M -> compound (Abs M)
| abs_active_compound: forall M, status M = 1 -> compound (Abs M)
.

Hint Resolve 
abs_op_compound op1_compound op2_compound abs_compound_compound abs_active_compound
.


Lemma rank_compound_l : forall M, compound M -> 
rank (left_component M) < rank M. 
Proof. 
split_all. inversion H; subst;  
eapply2 rank_component_app_l || 
eapply2 rank_component_abs_l || 
split_all. 
Qed. 

Lemma rank_compound_r : forall M, compound M -> 
rank (right_component M) < rank M. 
Proof. 
split_all. inversion H; subst;  
eapply2 rank_component_app_r || 
eapply2 rank_component_abs_r || 
inv1 compound.
Qed. 

Lemma lift_rec_preserves_compound : 
forall (M: lamSF), compound M -> forall (n k : nat), compound(lift_rec M n k).
Proof. 
intros M c; induction c; split_all. 
eapply2 abs_active_compound. 
assert(status (lift_rec M (S n) k) = relocate (status M) (S (S n)) k). 
eapply2 lift_rec_preserves_status. 
rewrite H0. rewrite H. relocate_lt. auto. 
Qed. 
Hint Resolve lift_rec_preserves_compound.

Lemma subst_rec_preserves_compound: 
forall (M: lamSF), compound M -> forall N (k : nat), compound(subst_rec M N k).
Proof. 
intros M c; induction c; split_all. 
eapply2 abs_active_compound. 
assert(status (subst_rec M N (S k)) = status M).
eapply2 subst_rec_preserves_status. omega. 
rewrite H0. auto.
Qed. 
Hint Resolve subst_rec_preserves_compound.

Lemma compound_not_active : forall M, compound M -> status M = 0.
Proof. intros M c; induction c; split_all; omega. Qed. 


Lemma star_compound : forall M, compound (star M).
Proof. induction M; split_all; try (case n); split_all; try (unfold_op; auto; fail).  Qed. 



Lemma  subst_rec_preserves_star_active : 
forall (M : lamSF) N k, status M <= (S k) -> 
  subst_rec(star M) N k = star (subst_rec M N (S k)).
Proof. 
induction M; split_all. 
gen_case H n. 
unfold insert_Ref.
elim(compare k n0); elim(compare (S k) (S n0));split_all; try noway. 
elim a; elim a0; split_all; try noway. 
elim a; split_all; try noway. 
elim a; split_all; try noway.
rewrite IHM. auto. omega. 
Qed. 

Lemma  subst_rec_preserves_star_compound : 
forall (M : lamSF) N k, compound M -> 
  subst_rec(star M) N k = star(subst_rec M N (S k)).
Proof. 
induction M; split_all; inversion H; split_all.
rewrite IHM; auto. 
rewrite subst_rec_preserves_star_active. auto. omega. 
Qed. 


Lemma  subst_rec_preserves_components_l : forall (M : lamSF) n k, compound M -> 
  subst_rec(left_component M) n k = left_component(subst_rec M n k).
Proof. induction M; split_all; inv1 compound. Qed. 


Lemma  subst_rec_preserves_components_active_r : 
forall (M : lamSF),  status M > 0 -> forall n k,  status M <= k ->  
subst_rec(right_component M) n k = right_component(subst_rec M n k).
Proof. 
induction M; split_all. 
(* 2 *) 
insert_Ref_out; split_all. 
rewrite subst_rec_preserves_star_active. 
auto. 
omega. 
Qed. 

Lemma  subst_rec_preserves_components_compound_r : 
forall (M : lamSF),  compound M -> forall n k,   
subst_rec(right_component M) n k = right_component(subst_rec M n k).
Proof. 
induction M; split_all; inversion H; subst; split_all.
rewrite subst_rec_preserves_star_compound. 
auto. 
auto. 
rewrite subst_rec_preserves_star_active. 
auto. 
omega. 
Qed. 

Definition preserves_compound (red:termred) := 
forall M, compound M -> forall N, red M N -> 
compound N /\ red (left_component M) (left_component N) /\ red(right_component M) (right_component N).


Lemma preserves_compound_seq : 
forall (red1 red2:termred), preserves_compound red1 -> preserves_compound red2 -> 
                            preserves_compound (sequential red1 red2). 
Proof. 
red; split_all.  
inversion H2. 
elim(H M H1 N0); split_all. 
eapply2 H0. 
inversion H2. 
elim(H M H1 N0); split_all. 
elim(H0 N0 H9 N); split_all. 
eapply2 seq_red. 
inversion H2. 
elim(H M H1 N0); split_all. 
elim(H0 N0 H9 N); split_all. 
eapply2 seq_red. 
Qed. 


Lemma preserves_compound_multi_step : 
forall (red:termred), preserves_compound red -> preserves_compound (multi_step red). 
Proof. 
red. intros red p M c N R; induction R; split_all. 
eapply2 IHR. eapply2 p.
apply succ_red with (left_component N); auto. 
 eapply2 p. eapply2 IHR. eapply2 p.
apply succ_red with (right_component N); auto. 
 eapply2 p. eapply2 IHR. eapply2 p.
Qed. 

Hint Resolve preserves_compound_multi_step.

(* Operator reduction  *) 


Inductive opred1 : termred :=
  | ref_opred : forall i, opred1 (Ref i) (Ref i)
  | op_opred : forall o, opred1 (Op o) (Op o)
  | app_opred :
      forall M M' ,
      opred1 M M' ->
      forall N N' : lamSF, opred1 N N' -> opred1 (App M N) (App M' N')  
  | abs_opred : forall M M' , opred1 M M' -> opred1 (Abs M) (Abs M')
  | s_red: forall (M M' N N' P P' : lamSF),
             opred1 M M' -> opred1 N N' -> opred1 P P' ->                  
             opred1 
                   (App (App (App s_op M) N) P) 
                  (App (App M' P') (App N' P'))
  | f_op_red : forall M  M' N o,  opred1 M M' -> 
               opred1 (App (App (App f_op (Op o)) M) N) M' 
  | f_compound_red: forall (P P' M N N': lamSF), compound P -> 
             opred1 P P' -> opred1 N N' -> 
             opred1 (App (App (App f_op P) M) N)
                     (App (App N' (left_component P')) (right_component P'))  .

Hint Resolve 
ref_opred op_opred app_opred abs_opred 
s_red f_op_red f_compound_red
.


Definition opred := multi_step opred1. 

Lemma reflective_opred1 : reflective opred1.
Proof. red; induction M; split_all. Qed. 
Hint Resolve reflective_opred1. 

Lemma reflective_opred : reflective opred.
Proof. unfold opred; eapply2 refl_multi_step. Qed. 
Hint Resolve reflective_opred. 



Lemma preserves_abs_opred : preserves_abs opred.
Proof. eapply2 preserves_abs_multi_step; red; split_all. Qed.
Hint Resolve  preserves_abs_opred. 

Lemma preserves_app_opred : preserves_app opred.
Proof. eapply2 preserves_app_multi_step. red; split_all. Qed.
Hint Resolve  preserves_app_opred. 


Lemma preserves_star_opred1_active : 
forall M, status M > 0 -> forall N, opred1 M N -> 
opred1 (star M) (star N). 
Proof. 
induction M; split_all. 
inversion H0. 
case n; split_all. 
noway. 
inversion H0; split_all; subst; simpl in *; try noway. 
eapply2 abs_opred. 
eapply2 IHM. omega. 
inversion H0; split_all; subst; simpl in *; try noway.
assert(status P = 0) by eapply2 compound_not_active.  noway. 
Qed. 

Lemma preserves_star_opred1_compound : 
forall M, compound M -> forall N, opred1 M N -> 
opred1 (star M) (star N). 
Proof. 
induction M; split_all; inv1 compound.  
(* 6 *) 
subst; inversion H0;   inversion H2; subst; split_all.
(* 5 *)  
unfold_op; split_all. subst; inversion H0; split_all. inversion H1; split_all. 
(* 4 *) 
subst; inversion H0.    assert(opred1 (star M) (star M')) by eapply2 IHM.  split_all. 
(* 3 *) 
subst; inversion H0.  simpl in *. eapply2 abs_opred.
eapply2 preserves_star_opred1_active. omega. 
(* 2 *) 
subst; inversion H0.   inversion H2. split_all. 
(* 1 *) 
subst; inversion H0.   inversion H2. inversion H7; split_all. 
Qed. 



Lemma  preserves_status_opred1: 
forall M, status M >0 -> forall N, opred1 M N -> status M = status N . 
Proof. 
cut(forall p M, p>= rank M -> status M >0 -> forall N, opred1 M N -> status M = status N). 
split_all; eapply2 H. 
induction p; split_all. 
assert(rank M >0) by eapply2 rank_positive. noway. 
(* p >0 *) 
induction M; intros. 
inversion H1; split_all.
simpl in *; noway.
inversion H1; split_all.
(* 2 *) 
cut(status M = status M'); split_all; eapply2 IHp; simpl in *; omega. 
(* 1 *) 
generalize IHM1 H H0 H1; clear IHM1 H H0 H1; case M1; intros.  
inversion H1. inversion H4; split_all. 
simpl in *; noway. 
simpl in H0. noway. 
(* 1 *) 
generalize IHM1 H H0 H1; clear IHM1 H H0 H1; case l; intros.  
inversion H1. inversion H4.  inversion H9; split_all. 
simpl in *; noway. 
simpl in *; noway. 
(* 1 *) 
generalize IHM1 H H0 H1; clear IHM1 H H0 H1; case l1; intros.  
inversion H1. inversion H4.  inversion H9.  inversion H14; split_all. 
generalize IHM1 H H0 H1; clear IHM1 H H0 H1; case o; split_all; try noway. 
inversion H1. inversion H4.  inversion H9.  inversion H14; split_all. 
eapply2 IHp. omega.
subst.  simpl in *. noway. 
assert(status l2 = 0) by eapply2 compound_not_active. noway. 
simpl in *; noway.
(* 1 *)
assert(status (App (App (App (App l3 l4) l2) l0) M2) = status  (App (App (App l3 l4) l2) l0)) by split_all. 
rewrite H2. rewrite H2 in H0. 
generalize H0; clear H0; inversion H1; intro. 
generalize H7; clear H7; inversion H4; intro. 
generalize H12; clear H12; inversion H9; intro. 
generalize H17; clear H17; inversion H14; intro. 
assert(status (App (App (App (App M'2 N'2) N'1) N'0) N') = status  (App (App (App M'2 N'2) N'1) N'0)) by split_all. 
rewrite H23. 
eapply2 IHp. 
simpl in *; omega. 
(* 9 *)
simpl in *; noway.  
simpl in *; noway.  
2: simpl in *; noway.  
2: simpl in *; noway.  
3: simpl in *; noway.  
3: simpl in *; noway.  
(* 3 *) 
simpl in H23. 
assert(status P = 0) by eapply2 compound_not_active. noway. 
(* 2 *) 
simpl in H19. 
assert(status P = 0) by eapply2 compound_not_active. noway. 
(* 1 *) 
simpl in H15. 
assert(status l4 = 0) by eapply2 compound_not_active. noway. 
Qed. 



Lemma  preserves_compound_opred1: 
forall M, compound M -> forall N, opred1 M N -> 
compound N /\ 
opred1 (left_component M) (left_component N) /\ 
opred1(right_component M) (right_component N). 
Proof. 
induction M; split_all.
(* 12 *) 
inv1 compound. 
inv1 compound. 
inv1 compound. 
inversion H. 
inversion H. 
inversion H.
(* 6 *) 
inversion H0; subst.
inversion H; subst.  
inversion H2; split_all.   
eapply2 abs_compound_compound. 
eapply2 IHM. 
eapply2 abs_active_compound. 
rewrite <- H3. eapply2 sym_eq. 
eapply2 preserves_status_opred1. omega. 
(* 5 *) 
inversion H0; subst; split_all. 
(* 4 *) 
inversion H0; subst.
inversion H; subst.  
inversion H2; split_all.   
(* 5 *) 
simpl in *. 
unfold_op; repeat(eapply2 app_opred). 
eapply2 preserves_star_opred1_compound. 
(* 4 *) 
unfold right_component; unfold_op; fold star; repeat(eapply2 app_opred). 
eapply2 preserves_star_opred1_active. omega. 
(* 3 *) 
inversion H; subst. 
inversion H0. inversion H3; subst; split_all. 
inversion H0. inversion H3; inversion H8; subst; split_all. 
(* 2 *) 
inversion H; subst. 
inversion H0. inversion H3; subst; split_all. 
inversion H0. inversion H3; inversion H8; subst; split_all. 
(* 1 *) 
inversion H; subst. 
inversion H0. inversion H3; subst; split_all. 
inversion H0. inversion H3; inversion H8; subst; split_all. 
Qed. 

Hint Resolve preserves_compound_opred1 .

Lemma  preserves_compound_opred: preserves_compound opred.
Proof. 
eapply2 preserves_compound_multi_step. 
split_all; eapply2 preserves_compound_opred1. 
Qed.
Hint Resolve preserves_compound_opred .



Lemma lift_rec_preserves_opred1 : lift_rec_preserves opred1.
Proof. red. induction 1;  split_all.
relocate_lt. 
rewrite lift_rec_preserves_components_l. 
rewrite lift_rec_preserves_components_r. 
auto. 
Qed. 

Hint Resolve lift_rec_preserves_opred1.

Lemma lift_rec_preserves_opred : lift_rec_preserves opred.
Proof. eapply2 lift_rec_preserves_multi_step. Qed.
Hint Resolve lift_rec_preserves_opred. 

Lemma subst_rec_preserves_opred1 : subst_rec_preserves opred1. 
Proof. 
red. 
intros M M' R; induction R; split_all. 
(* 2 *) 
unfold insert_Ref. elim(compare k i); split_all. elim a; split_all. 
unfold lift. eapply2 lift_rec_preserves_opred1. 
(* 1 *) 
assert(compound P') by eapply2 preserves_compound_opred1. 
rewrite subst_rec_preserves_components_l; split_all.
rewrite subst_rec_preserves_components_compound_r; split_all.
Qed. 

Ltac app_op := unfold_op; 
match goal with 
| |- opred _ _ => red; app_op
| |- multi_step opred1 (Op _) (Op _) => red; one_step; app_op
| |- multi_step opred1 (Abs _) (Abs _) => eapply2 preserves_abs_opred ; app_op
| |- multi_step opred1 (App _ _) (App _ _) => eapply2 preserves_app_opred ; app_op
| |- multi_step opred1 (left_component _) (left_component _) => eapply2 preserves_compound_opred; app_op 
| |- multi_step opred1 (right_component _) (right_component _) => eapply2 preserves_compound_opred; app_op
| |- multi_step opred1 (lift_rec _ _ _) (lift_rec _ _ _) => eapply2 lift_rec_preserves_opred; app_op
| |- opred1 (Abs _) (Abs _) => eapply2 abs_opred ; app_op
| |- opred1 (App _ _) (App _ _) => eapply2 app_opred ; app_op
| |- opred1 (left_component _) (left_component _) => eapply2 preserves_compound_opred1; app_op 
| |- opred1 (right_component _) (right_component _) => eapply2 preserves_compound_opred1; app_op
| |- opred1 (lift_rec _ _ _) (lift_rec _ _ _) => eapply2 lift_rec_preserves_opred1; app_op
| H : opred1 _ _ |- compound _ => eapply2 preserves_compound_opred1
| |- opred1 (left_component _) _ => eapply2 preserves_compound_opred1
| |- opred1 (right_component _) _ => eapply2 preserves_compound_opred1
| _ => try red; split_all
end.




Ltac opred_compound := 
fold opred in *; 
match goal with 
| H : opred   (App (App (Op ?o) ?M1) ?M2) ?N |- _ => 
assert(opred  (right_component (App (App (Op o) M1) M2))
          (right_component N)) by 
eapply2 preserves_compound_opred;
assert(opred  (left_component (App (App (Op o) M1) M2))
          (left_component N)) by 
eapply2 preserves_compound_opred; simpl in *; clear H; opred_compound
| H : opred (App (Op ?o) ?M1) ?N  |- _ => 
assert(opred  (right_component (App (Op o) M1))
          (right_component N)) by 
eapply2 preserves_compound_opred; clear H; opred_compound
| _ => simpl in *
end;
simpl in *.


(* Diamond Lemmas *) 


Lemma diamond_opred1_opred1 : diamond opred1 opred1. 
Proof.  
red; intros M N OR; induction OR; split_all; eauto.

(* 5 subgoals *)
inversion H; clear H; subst; inv opred1; inv opred1; eauto. 

(* 8 subgoals *) 
elim(IHOR1 M'0); elim(IHOR2 N'0); split_all. eauto.
(* 7 *)
elim(IHOR1 (App (App s_op M'0) N'0)); 
elim(IHOR2 P'); split_all.  unfold s_op in *; inv opred1. 
invsub. exist(App (App N'4 x) (App N'3 x)). 
(* 6 *) 
inversion H7. 
elim (IHOR1 (App (App f_op (Op o)) P)); split_all. 
unfold f_op in *; inv opred1. 
invsub. exist N'1. 
(* 5 *) 
unfold f_op in *. 
elim (IHOR1 (App (App f_op P') N'1)); elim (IHOR2 N'0); split_all. 
inv opred1.  invsub. 
exist(App (App x (left_component N'4)) (right_component N'4)). 
eapply2 f_compound_red. 
eapply2 preserves_compound_opred1. 
app_op. 
(* 4 *) 
inversion H; subst. elim(IHOR M'0); split_all.  exist (Abs x). 
(* 3 *) 
unfold s_op in *. inv opred1. invsub. 
elim(IHOR1 N'2); elim(IHOR2 N'1); elim(IHOR3 N'0); split_all. 
exist(App (App x1 x)(App x0 x)).
elim(IHOR1 M'0); elim(IHOR2 N'0); elim(IHOR3 P'0); split_all.
invsub.  
exist(App (App x1 x)(App x0 x)).
(* 2 *) 
inversion H.  inversion H2. inversion H7. inversion H12. inversion H14. 
elim(IHOR N'0); split_all. exist x. 
elim(IHOR P); split_all. 
inversion H3. 
(* 1 *) 
gen_inv H H0.  inversion H2. inversion H8. inversion H13. 
elim(IHOR1 N'2); elim(IHOR2 N'0); split_all. 
exist (App (App x (left_component x0)) (right_component x0)). 
app_op. 
eapply2 f_compound_red. 
eapply2 preserves_compound_opred1. 
inversion H5. 
elim(IHOR1 P'0); elim(IHOR2 N'0); split_all. 
exist (App (App x (left_component x0)) (right_component x0)). 
app_op. app_op. 
Qed. 


Hint Resolve diamond_opred1_opred1.

Lemma diamond_opred1_opred : diamond opred1 opred.
Proof. eapply2 diamond_strip. Qed. 

Lemma diamond_opred : diamond opred opred.
Proof.  eapply2 diamond_tiling. Qed. 
Hint Resolve diamond_opred.




Definition bop1  := sequential par_red1 opred.
Definition bop := multi_step bop1.

Lemma reflective_bop1: reflective bop1. 
Proof. red; reflect. apply seq_red with M; auto. Qed. 
Hint Resolve reflective_bop1.

Lemma preserves_abs_bop : preserves_abs bop.
Proof. eapply2 preserves_abs_multi_step; eapply2 preserves_abs_seq; red; split_all. Qed.
Hint Resolve  preserves_abs_bop. 

Lemma preserves_app_bop1 : preserves_app bop1.
Proof. eapply2 preserves_app_seq; red; split_all. Qed.
Hint Resolve  preserves_app_bop1. 

Lemma preserves_app_bop : preserves_app bop.
Proof. eapply2 preserves_app_multi_step.  Qed.
Hint Resolve  preserves_app_bop. 

Lemma lift_rec_preserves_bop1 : lift_rec_preserves bop1.
Proof. eapply2 lift_rec_preserves_seq. Qed. 
Hint Resolve lift_rec_preserves_bop1.

Lemma lift_rec_preserves_bop : lift_rec_preserves bop.
Proof. eapply2 lift_rec_preserves_multi_step. Qed.
Hint Resolve lift_rec_preserves_bop. 

Lemma subst_rec_preserves_bop1 : subst_rec_preserves bop1.
Proof. 
eapply2 subst_rec_preserves_seq.
eapply2 subst_rec_preserves_par_red1. 
eapply2 subst_rec_preserves_multi_step. 
red; split_all;  eapply2 subst_rec_preserves_opred1. 
red; split_all;  eapply2 subst_rec_preserves_opred1. 
Qed. 
Hint Resolve subst_rec_preserves_bop1.

Lemma subst_rec_preserves_bop : subst_rec_preserves bop.
Proof. eapply2 subst_rec_preserves_multi_step. 
red; split_all;  eapply2 subst_rec_preserves_bop1. 
red; split_all;  eapply2 subst_rec_preserves_bop1. 
Qed.
Hint Resolve subst_rec_preserves_bop. 



(* compounds *) 

Lemma preserves_status_par_red1 : 
forall M, status M > 0 -> forall N, par_red1 M N -> status M = status N.
Proof. 
cut(forall p M, p >= rank M -> status M > 0 -> forall N, par_red1 M N -> status M = status N). 
split_all; eapply2 H. 
induction p. 
split_all. assert(rank M > 0) by eapply2 rank_positive. noway. 
(* p > 0 *) 
induction M; intros.
inversion H1; split_all.
inversion H1; split_all.
inversion H1; split_all.
assert(status M = status M') . 
eapply2 IHM. simpl in *; omega. simpl in *; omega. auto. 
(* 1 *) 
generalize IHM1 H H0 ; clear IHM1 H H0; inversion H1; intros; try noway. 
simpl in H6. noway. 
generalize IHM1 H2 H5 H6; clear IHM1 H2 H5 H6. case M1; intros; try noway. 
inversion H2; split_all. 
inversion H2; split_all. 
simpl in H6. noway. 
(* 1 *) 
generalize IHM1 H5 H6 ; clear IHM1 H5 H6; inversion H2; intros; try noway. 
simpl in H11. noway. 
subst. clear H1 H2. 
(* 1 *) 
generalize IHM1 H7 H10 H11; clear IHM1 H7 H10 H11. case l; intros; try noway. 
inversion H7; split_all. 
inversion H7; split_all. 
simpl in H11. noway. 
(* 1 *) 
generalize IHM1 H7 H10 H11; clear IHM1 H7 H10 H11. case l1; intros; try noway. 
inversion H7. inversion H1; split_all. 
inversion H7. inversion H1; split_all. 
gen2_case IHM1 H11 o. 
eapply2 IHp. 
simpl in *; omega. 
simpl in H11. noway. 
(* 1 *) 
generalize IHM1 H10 H11 ; clear IHM1 H10 H11; inversion H7; intros; try noway. 
generalize IHM1 H10 H11 ; clear IHM1 H10 H11; inversion H1; intros; try noway. 
simpl in H13. noway. 
assert( status (App (App (App (App l3 l4) l2) l0) M2) = status (App (App (App l3 l4) l2) l0)). 
split_all. 
rewrite H14 in H13. rewrite H14. 
assert( status (App (App (App (App M'1 N'2) N'1) N'0) N') = status(App (App (App M'1 N'2) N'1) N'0)) by split_all. 
rewrite H15.
eapply2 IHp. 
simpl in *; omega. 
Qed. 



Lemma preserves_star_par_red1_active : 
forall M N, status M > 0 -> 
par_red1 M N -> par_red1 (star M) (star N).
Proof.
induction M; split_all. 
(* 4 *) 
inversion H0; subst; case n; split_all. 
noway. 
inversion H0; split_all. 
eapply2 abs_par_red. 
eapply2 IHM. omega. 
gen2_inv IHM1 H H0; subst; try noway. 
Qed. 


Lemma preserves_star_par_red1_compound : 
forall M N, compound M -> 
par_red1 M N -> par_red1 (star M) (star N).
Proof.
induction M; split_all. 
(* 4 *) 
inversion H. 
inversion H. 
(* 2 *) 
inversion H0; subst. simpl. 
eapply2 abs_par_red. 
gen_inv H2 H. 
inversion H1. split_all. 
eapply2 preserves_star_par_red1_active. omega. 
(* 1 *) 
gen2_inv IHM1 H H0; subst.  inversion H5.
Qed. 

Lemma preserves_compound_par_red1 : preserves_compound par_red1.
Proof.  
red. induction M; intros.  
(* 4 *) 
gen_inv H0 H; try (inversion H4); subst; inv par_red1; unfold_op.  
(* 3 *) 
inversion H.
(* 2 *) 
inversion H0; subst.  
inversion H; subst. 
(* 4 *) 
inversion H2; split_all.  
elim(IHM H3 M'); split_all. 
unfold_op. repeat (eapply2 app_par_red). 
eapply2 preserves_star_par_red1_compound.
(* 2 *) 
assert(status M = status M').  eapply2 preserves_status_par_red1. omega. 
split_all. 
eapply2 abs_active_compound. 
omega. 
eapply2 preserves_star_par_red1_active. omega. 
(* 1 *) 
inversion H0; subst; split_all; inversion H; subst; split_all;
inversion H3; split_all; inversion H4; split_all. 
Qed.

Hint Resolve preserves_compound_par_red1.

Lemma preserves_compound_par_red : preserves_compound par_red.
Proof.  red; eapply2 preserves_compound_multi_step. Qed.  


Ltac app_par := 
match goal with 
| |- par_red1 (left_component _) (left_component _) => eapply2 preserves_compound_par_red1; app_par 
| |- par_red1 (right_component _) (right_component _) => eapply2 preserves_compound_par_red1; app_par
| |- par_red1 (Abs _) (Abs _) => eapply2 abs_par_red ; app_par
| |- par_red1 (App _ _) (App _ _) => eapply2 app_par_red ; app_par
| |- par_red1 (subst_rec _ _ _) (subst_rec _ _ _) => eapply2 subst_rec_preserves_par_red1; app_par
| H : par_red1 _ _ |- compound _ => eapply2 preserves_compound_par_red1
| |- par_red1 (left_component _) _ => eapply2 preserves_compound_par_red1
| |- par_red1 (right_component _) _ => eapply2 preserves_compound_par_red1
| _ => try red; split_all
end.

Lemma  preserves_compound_bop1: preserves_compound bop1.
Proof. eapply2 preserves_compound_seq. Qed.
Hint Resolve preserves_compound_bop1 .

Lemma  preserves_compound_bop: preserves_compound bop.
Proof. eapply2 preserves_compound_multi_step. Qed.
Hint Resolve preserves_compound_bop .



Ltac app_bop := unfold_op; 
match goal with 
| |- bop _ _ => red; app_bop
| |- multi_step bop1 (Op _) (Op _) => red; one_step; app_bop
| |- multi_step bop1 (Abs _) (Abs _) => eapply2 preserves_abs_opred ; app_bop
| |- multi_step bop1 (App _ _) (App _ _) => eapply2 preserves_app_bop ; app_bop
| |- multi_step bop1 (left_component _) (left_component _) => eapply2 preserves_compound_opred; app_bop 
| |- multi_step bop1 (right_component _) (right_component _) => eapply2 preserves_compound_opred; app_bop
| |- multi_step bop1 (lift_rec _ _ _) (lift_rec _ _ _) => eapply2 lift_rec_preserves_opred; app_bop
| |- bop1 (Abs _) (Abs _) => eapply2 abs_opred ; app_bop
| |- bop1 (App _ _) (App _ _) => eapply2 preserves_app_bop ; app_bop
| |- bop1 (left_component _) (left_component _) => eapply2 preserves_compound_bop1; app_bop 
| |- bop1 (right_component _) (right_component _) => eapply2 preserves_compound_bop1; app_bop
| |- bop1 (lift_rec _ _ _) (lift_rec _ _ _) => eapply2 lift_rec_preserves_bop1; app_bop
| H : bop1 _ _ |- compound _ => eapply2 preserves_compound_bop1
| |- bop1 (left_component _) _ => eapply2 preserves_compound_bop1
| |- bop1 (right_component _) _ => eapply2 preserves_compound_bop1
| _ => try red; split_all
end.



Ltac bop_compound := 
fold bop in *; 
match goal with 
| H : bop   (App (App (Op ?o) ?M1) ?M2) ?N |- _ => 
assert(bop  (right_component (App (App (Op o) M1) M2))
          (right_component N)) by 
eapply2 preserves_compound_bop;
assert(bop  (left_component (App (App (Op o) M1) M2))
          (left_component N)) by 
eapply2 preserves_compound_bop; simpl in *; clear H; bop_compound
| H : bop (App (Op ?o) ?M1) ?N  |- _ => 
assert(bop  (right_component (App (Op o) M1))
          (right_component N)) by 
eapply2 preserves_compound_bop; clear H; bop_compound
| _ => simpl in *
end;
simpl in *.

(* Diamond Lemmas *) 


Lemma par_red1_preserves_components_l : 
forall M, compound M -> forall N, par_red1 M N -> 
par_red1 (left_component M) (left_component N). 
Proof. split_all. gen_inv H H0; inv1 compound. Qed. 


Lemma par_red1_preserves_components_r : 
forall M, compound M -> forall N, par_red1 M N -> 
par_red1 (right_component M) (right_component N). 
Proof. 
split_all. gen_inv H H0; inv1 compound. 
subst; inversion H; split_all. 
unfold_op; repeat (eapply2 app_par_red). 
eapply2 preserves_star_par_red1_compound.
eapply2 preserves_star_par_red1_active. omega. 
Qed. 




Lemma diamond_opred1_par_red1: diamond opred1 par_red1. 
Proof. 
red. intros M N R; induction R; split_all; inv par_red1; eauto.
inv opred1; inv par_red1. 

(* 6 *) 
elim(IHR1 (Abs M'0)); elim(IHR2 N'0); split_all. 
inv par_red1. inv opred1. 
exist(subst x M'). 
unfold subst. eapply2 subst_rec_preserves_opred1. 
(* 5 *)
elim(IHR1 M'0); elim(IHR2 N'0); split_all. exist(App x0 x). 
(* 4 *) 
elim(IHR M'0); split_all. exist(Abs x). 
(* 3 *) 
unfold s_op in *. inv par_red1. 
elim(IHR1 N'2); elim(IHR2 N'1); elim(IHR3 N'0); split_all. 
exist(App (App x1 x)(App x0 x)). 
(* 2 *) 
inversion H10. elim(IHR N'0); split_all. exist x. 
(* 1 *) 
elim(IHR1 N'2); elim(IHR2 N'0); split_all. 
exist(App (App x (left_component x0)) (right_component x0)). 
eapply2 app_par_red. eapply2 app_par_red. 
assert(compound P') by eapply2 preserves_compound_opred1. 
eapply2 par_red1_preserves_components_l. 
assert(compound P') by eapply2 preserves_compound_opred1. 
eapply2 par_red1_preserves_components_r. 
inversion H11. 
eapply2 f_compound_red. 
eapply2 preserves_compound_par_red1. 
Qed. 


Lemma diamond_opred_par_red1: diamond opred par_red1. 
Proof. 
eapply2 diamond_flip. 
eapply2 diamond_strip. 
eapply2 diamond_flip. 
eapply2 diamond_opred1_par_red1. 
Qed.

Lemma diamond_bop1 : diamond bop1 bop1.
Proof. 
red. split_all. inversion H; subst. inversion H0; subst. 
elim(parallel_moves M N0 H1 N1); split_all. 
elim(diamond_opred_par_red1 N0 N H2 x); split_all. 
elim(diamond_opred_par_red1 N1 P H4 x); split_all. 
elim(diamond_opred x x1 H11 x0); split_all. 
exist x2. 
apply seq_red with x0; split_all. 
apply seq_red with x1; split_all. 
Qed. 

Lemma diamond_bop : diamond bop bop.
Proof. eapply2 diamond_tiling. eapply2 diamond_bop1. Qed. 


Theorem confluence_lamSF_bop:  confluence lamSF bop. 
Proof.
red; split_all. eapply2 diamond_bop. Qed. 
