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
(*                LambdaFactor Calculus                               *)
(*                                                                    *)
(* is implemented in Coq by adapting the implementation of            *)
(* Lambda Calculus from Project Coq                                   *)
(* 2015                                                               *)
(**********************************************************************)

(**********************************************************************)
(*                   Primitive_Recursion.v                            *)
(*                                                                    *)
(*                     Barry Jay                                      *)
(*                                                                    *)
(**********************************************************************)


Require Import Arith.
Require Import Max. 
Require Import Test.
Require Import General. 
Require Import "Lambda/Terms".
Require Import "Lambda/Lambda_tactics".
Require Import "Lambda/Substitution_term".
Require Import "Lambda/Reduction".
Require Import "Lambda/Redexes".
Require Import "Lambda/Substitution".
Require Import "Lambda/Residuals".
Require Import "Lambda/Marks".
Require Import "Lambda/Simulation".
Require Import "Lambda/Cube".
Require Import "Lambda/Confluence".
Require Import "Lambda/Closed".
Require Import LamSF_Terms.
Require Import LamSF_Tactics.
Require Import LamSF_Substitution_term.
Require Import SF_reduction.
Require Import LamSF_reduction.
Require Import LamSF_Normal.
Require Import LamSF_Closed.
Require Import LamSF_Eval.
Require Import Unstar.
Require Import List. 


(* Represent primitive and general recursive functions on natural numbers as normal forms of lamSF.
If f(x__{n-1},...,x_0) is such as function then f is represented by some term P = Abs (..(Abs ...))
Free variables represent formal parameters of the function  *) 



Lemma status_subst_app_ref_lt : forall M k, status M < S k -> forall N i, status (subst_rec M (App (Ref i) N) k) = status M.
Proof. 
cut(forall p M, p>= rank M -> forall k, status M  < S k -> forall N i, status (subst_rec M (App (Ref i) N) k) = status M).
split_all. eapply2 H. 
induction p. split_all. assert(rank M >0) by eapply2 rank_positive. noway. 
induction M; intros. 
(* 4 *) 
simpl in *; inversion H0; subst. insert_Ref_out. auto.
 insert_Ref_out. auto. 
(* 3 *) 
split_all. 
(* 2 *) 
split_all. 
simpl in *;  
assert(status (subst_rec M (App (Ref i) N) (S k)) = status M).
eapply2 IHM. omega. 
omega. 
omega. 
(* 1 *) 
clear IHM2. 
unfold subst_rec; fold subst_rec. 
generalize  IHM1 H H0; clear IHM1 H H0; case M1; intros; try (simpl in *; split_all; fail). 
simpl in *; split_all. 
inversion H0; subst. insert_Ref_out. split_all. 
insert_Ref_out. split_all. 
generalize  IHM1 H H0; clear IHM1 H H0; case l; intros; try (simpl in *; split_all; fail). 
unfold subst_rec; fold subst_rec.
simpl in H0.  
insert_Ref_out. split_all. 
generalize  IHM1 H H0; clear IHM1 H H0; case l1; intros; try (simpl in *; split_all; fail). 
unfold subst_rec; fold subst_rec.
simpl in H0.  
insert_Ref_out. split_all. 
simpl in *; split_all. 
generalize  IHM1 H H0; clear IHM1 H H0; case o; intros; try (simpl in *; split_all; fail). 
eapply2 IHp. 
omega. 
generalize  IHM1 H H0; clear IHM1 H H0; case l3; intros; try (simpl in *; split_all; fail). 
unfold subst_rec; fold subst_rec.
simpl in H0.  
insert_Ref_out. split_all.
generalize  IHM1 H H0; clear IHM1 H H0; case o; intros; try (simpl in *; split_all; fail). 
split_all. 
eapply2 IHp. 
simpl in *; omega.
unfold subst_rec; fold subst_rec.  
replace  (status
     (App
        (App
           (App
              (App
                 (App (subst_rec l5 (App (Ref i) N) k)
                    (subst_rec l6 (App (Ref i) N) k))
                 (subst_rec l4 (App (Ref i) N) k))
              (subst_rec l2 (App (Ref i) N) k))
           (subst_rec l0 (App (Ref i) N) k)) (subst_rec M2 (App (Ref i) N) k))) with 
(status (subst_rec (App
           (App
              (App
                 (App l5 l6) l4) l2) l0)  (App (Ref i) N) k)) by auto.
replace(status (App (App (App (App (App l5 l6) l4) l2) l0) M2)) with 
(status (App (App (App (App l5 l6) l4) l2) l0)) by auto. 
eapply2 IHp. 
simpl in *. omega. 
Qed. 



Lemma status_subst_app_ref_gt : forall M k, status M > S k -> forall N i, status (subst_rec M (App (Ref i) N) k) = pred(status M).
Proof. 
cut(forall p M, p>= rank M -> forall k, status M  > S k -> forall N i, status (subst_rec M (App (Ref i) N) k) = pred(status M)).
split_all. eapply2 H. 
induction p. split_all. assert(rank M >0) by eapply2 rank_positive. noway. 
induction M; intros. 
(* 4 *) 
simpl in *; inversion H0; subst. insert_Ref_out. auto.
 insert_Ref_out. replace n with (S (pred n)) by omega. auto. 
(* 3 *) 
split_all. 
(* 2 *) 
split_all. 
simpl in *;  
assert(status (subst_rec M (App (Ref i) N) (S k)) = pred(status M)).
eapply2 IHM. omega. 
omega. 
omega. 
(* 1 *) 
clear IHM2. 
unfold subst_rec; fold subst_rec. 
generalize  IHM1 H H0; clear IHM1 H H0; case M1; intros; try (simpl in *; split_all; fail). 
simpl in *; split_all. 
inversion H0; subst. insert_Ref_out. split_all. 
insert_Ref_out. replace n with (S (pred n)) by omega.  split_all. 
generalize  IHM1 H H0; clear IHM1 H H0; case l; intros; try (simpl in *; split_all; fail). 
unfold subst_rec; fold subst_rec.
simpl in H0.  
insert_Ref_out. split_all. omega. 
generalize  IHM1 H H0; clear IHM1 H H0; case l1; intros; try (simpl in *; split_all; fail). 
unfold subst_rec; fold subst_rec.
simpl in H0.  
insert_Ref_out. split_all. omega. 
simpl in *; split_all. 
generalize  IHM1 H H0; clear IHM1 H H0; case o; intros; try (simpl in *; split_all; fail). 
eapply2 IHp. 
omega. 
generalize  IHM1 H H0; clear IHM1 H H0; case l3; intros; try (simpl in *; split_all; fail). 
unfold subst_rec; fold subst_rec.
simpl in H0.  
insert_Ref_out. split_all. omega. 
generalize  IHM1 H H0; clear IHM1 H H0; case o; intros; try (simpl in *; split_all; fail). 
split_all. 
eapply2 IHp. 
simpl in *; omega.
unfold subst_rec; fold subst_rec.  
replace  (status
     (App
        (App
           (App
              (App
                 (App (subst_rec l5 (App (Ref i) N) k)
                    (subst_rec l6 (App (Ref i) N) k))
                 (subst_rec l4 (App (Ref i) N) k))
              (subst_rec l2 (App (Ref i) N) k))
           (subst_rec l0 (App (Ref i) N) k)) (subst_rec M2 (App (Ref i) N) k))) with 
(status (subst_rec (App
           (App
              (App
                 (App l5 l6) l4) l2) l0)  (App (Ref i) N) k)) by auto.
replace(status (App (App (App (App (App l5 l6) l4) l2) l0) M2)) with 
(status (App (App (App (App l5 l6) l4) l2) l0)) by auto. 
eapply2 IHp. 
simpl in *. omega. 
Qed. 




Lemma status_subst_app_ref_eq : forall M k, status M  = S k -> forall N i, status (subst_rec M (App (Ref i) N) k) = S(i+k).
Proof. 
cut(forall p M, p>= rank M -> forall k, status M  = S k -> forall N i, status (subst_rec M (App (Ref i) N) k) = S(i+k)).
split_all. eapply2 H. 
induction p. split_all. assert(rank M >0) by eapply2 rank_positive. noway. 
induction M; intros. 
(* 4 *) 
simpl in *; inversion H0; subst. insert_Ref_out. 
unfold relocate. elim(test 0 i); split_all; omega. simpl in *; noway.
simpl in *;  
assert(status (subst_rec M (App (Ref i) N) (S k)) = S (i + S k)). 
eapply2 IHM. omega. 
omega. 
omega. 
(* 1 *) 
clear IHM2. 
unfold subst_rec; fold subst_rec. 
generalize  IHM1 H H0; clear IHM1 H H0; case M1; intros; try (simpl in *; split_all; fail). 
simpl in *; split_all. 
inversion H0; subst. insert_Ref_out. simpl. unfold relocate. elim(test 0 i); split_all; try noway. omega. 
generalize  IHM1 H H0; clear IHM1 H H0; case l; intros; try (simpl in *; split_all; fail). 
simpl in *; split_all. 
inversion H0; subst. insert_Ref_out. simpl. unfold relocate. elim(test 0 i); split_all; try noway. omega. 
generalize  IHM1 H H0; clear IHM1 H H0; case l1; intros; try (simpl in *; split_all; fail). 
simpl in *; split_all. 
inversion H0; subst. insert_Ref_out. simpl. unfold relocate. elim(test 0 i); split_all; try noway. omega. 
generalize  IHM1 H H0; clear IHM1 H H0; case o; intros; try (simpl in *; split_all; fail). 
simpl in *; split_all. 
eapply2 IHp. 
omega. 
generalize  IHM1 H H0; clear IHM1 H H0; case l3; intros; try (simpl in *; split_all; fail). 
simpl in *; split_all. 
inversion H0; subst. insert_Ref_out. simpl. unfold relocate. elim(test 0 i); split_all; try noway. omega. 
generalize  IHM1 H H0; clear IHM1 H H0; case o; intros; try (simpl in *; split_all; fail). 
simpl in *; split_all. 
eapply2 IHp. 
omega. 
unfold subst_rec; fold subst_rec.
replace  (status
     (App
        (App
           (App
              (App
                 (App (subst_rec l5 (App (Ref i) N) k)
                    (subst_rec l6 (App (Ref i) N) k))
                 (subst_rec l4 (App (Ref i) N) k))
              (subst_rec l2 (App (Ref i) N) k))
           (subst_rec l0 (App (Ref i) N) k)) (subst_rec M2 (App (Ref i) N) k))) with 
(status (subst_rec (App
           (App
              (App
                 (App l5 l6) l4) l2) l0)  (App (Ref i) N) k)) by auto. 
eapply2 IHp. 
simpl in *. omega. 
Qed. 

Lemma status_subst_app_ref : forall M k, status M  >0 -> forall N i, status (subst_rec M (App (Ref i) N) k) >0.
Proof. 
intros. assert(status M < S k \/  status M > S k \/ status M = S k) by omega. 
inversion H0. 
rewrite status_subst_app_ref_lt. auto. auto. 
inversion H1. 
rewrite status_subst_app_ref_gt. omega. auto. 
rewrite status_subst_app_ref_eq. omega. auto. 
Qed. 



Lemma normal_subst_app_ref : forall M, normal M -> forall N i k, normal N -> normal (subst_rec M (App (Ref i) N) k).
Proof. 
intros M nor; induction nor; split_all. 
unfold insert_Ref. elim(compare k n); split_all. elim a; split_all. 
unfold lift. 
eapply2 lift_rec_preserves_normal. eapply2 nf_active. simpl; omega. 
eapply2 nf_active. 
replace  (App (subst_rec M1 (App (Ref i) N) k) (subst_rec M2 (App (Ref i) N) k)) with 
(subst_rec (App M1 M2) (App (Ref i) N) k) by auto.
eapply2 status_subst_app_ref. 
eapply2 nf_compound. 
replace  (App (subst_rec M1 (App (Ref i) N) k) (subst_rec M2 (App (Ref i) N) k)) with 
(subst_rec (App M1 M2) (App (Ref i) N) k) by auto.
eapply2 subst_rec_preserves_compound. 
Qed. 


Lemma wait_normal: forall M N, normal M -> normal N -> normal (wait M N). 
Proof. unfold wait; unfold_op; split_all. repeat (eapply2 nf_compound).  Qed. 

Lemma little_omega_normal: normal little_omega. 
Proof. 
unfold little_omega. 
eapply2 nf_abs. 
eapply2 nf_abs. 
eapply2 nf_active. 
eapply2 nf_active. 
eapply2 nf_active. 
simpl. omega. 
simpl. omega. 
Qed. 


(* eager evaluation *) 

Definition eager M N := App (App (App (App f_op N)
                                       (Abs (App (Ref 0) (lift_rec N 0 1))))
                                  (App k_op (App k_op (Abs (App (Ref 0) (lift_rec N 0 1)))))) M
.

Lemma eager_is_eager : forall M N, factorable N -> lamSF_red (eager M N) (App M N).
Proof. 
intros M N fact; inversion fact; split_all; subst; unfold eager; split_all. 
(* 2 *) 
eval_lamSF0. insert_Ref_out. rewrite lift_rec_null.  auto. 
(* 1 *) 
unfold_op. 
apply transitive_red with (App
        (App (App 
           (App (App (Op Fop) (Op Fop))
              (App (App (Op Fop) (Op Fop))
                 (Abs (App (Ref 0) (lift_rec N 0 1))))) (left_component N))  (right_component N)) M). 
eapply2 preserves_app_lamSF_red. 
eval_lamSF0. insert_Ref_out. rewrite lift_rec_null. 
eapply2 preserves_app_lamSF_red. 
rewrite subst_rec_lift_rec; try omega. rewrite lift_rec_null. auto. 
Qed. 

(* 
Lemma eager_may_pause : forall M N, (factorable N -> False) -> forall P, lamSF_red (App (App eager M) N) P -> 
exists M' N', P = App (App eager M' N') /\ lamSF_red M M' /\ lamSF_red N N'
*) 

Lemma eager_normal: forall M N, normal M -> normal N -> status N >0  -> normal (eager M N).
Proof. 
induction N; split_all; unfold eager; split_all; unfold_op. 
eapply2 nf_active. 
eapply2 nf_active. 
eapply2 nf_compound. 
eapply2 nf_compound. 
eapply2 nf_compound. 
noway. 
eapply2 nf_active. 
eapply2 nf_active. 
eapply2 nf_compound. 
eapply2 nf_abs. 
eapply2 nf_active. 
eapply2 nf_abs. 
inversion H0. 
eapply2 lift_rec_preserves_normal. 
eapply2 nf_compound. 
eapply2 nf_compound. 
eapply2 nf_abs. 
eapply2 nf_active. 
eapply2 nf_abs. 
inversion H0. 
eapply2 lift_rec_preserves_normal. 
(* 1 *)
eapply2 nf_active. 
eapply2 nf_active. 
eapply2 nf_compound. 
eapply2 nf_abs. 
eapply2 nf_active. 
replace (App (lift_rec N1 0 1) (lift_rec N2 0 1)) with (lift_rec (App N1 N2) 0 1) by auto. 
eapply2 lift_rec_preserves_normal. 
eapply2 nf_compound. 
eapply2 nf_compound. 
eapply2 nf_abs. 
eapply2 nf_active. 
replace (App (lift_rec N1 0 1) (lift_rec N2 0 1)) with (lift_rec (App N1 N2) 0 1) by auto. 
eapply2 lift_rec_preserves_normal. 
Qed. 


Definition fix_eager M N := eager (wait (wait little_omega little_omega) M) N.
Definition fix2 := Abs (Abs (fix_eager (Ref 1) (Ref 0))).


Fixpoint natrep (n: nat) : lamSF  := 
match n with 
| 0 => s_op 
| S n0 => App s_op (natrep n0)
end. 

Fixpoint composition_body1 (f: lamSF) (gs : list lamSF) :=  
(* assume length gs = arity of f, m = arity of gs *) 
match gs with 
| nil => f
| cons g gs1 => composition_body1 (subst g f) gs1 
end. 

Definition composition_body f gs := composition_body1 (lift (length gs) f) gs. 

Definition primrec_body (f g : lamSF) := fix_eager (Abs (Abs 
(App (App (App f_op (Ref 0)) (lift 2 f)) (App k_op (Abs (subst_rec (lift_rec g 2 3) (App (Ref 2) (Ref 0)) 1)))))) (Ref 0).

Definition leastrec_body (f: lamSF) := 
match f with 
| Op _ => f 
| App (App (App (Op Fop) _) _) _ => 
   fix_eager (Abs (Abs (App (App (App f_op (lift_rec f 1 1)) (Ref 0)) 
                            (App k_op (App k_op (App (Ref 1) (App s_op (Ref 0)))))))) 
             (Ref 0)
| _ => f_op (* the undefined function *) 
end.

Lemma composition_body_normal : 
forall gs, (forall g, In g gs -> normal g) -> forall f, normal f -> normal (composition_body f gs). 
Proof. 
induction gs; split_all; unfold composition_body; unfold lift; split_all; unfold composition_body1; fold composition_body1; split_all. 
rewrite lift_rec_null. auto. 
unfold subst. rewrite subst_rec_lift_rec; try omega. 
eapply2 IHgs. 
Qed. 

 Lemma primrec_body_normal : forall f g, normal f -> normal g -> normal (primrec_body f g). 
Proof. 
split_all. unfold primrec_body. unfold_op. 
eapply2 eager_normal. 
eapply2 wait_normal. 
eapply2 wait_normal. 
eapply2 little_omega_normal. 
eapply2 little_omega_normal. 
eapply2 nf_abs. 
eapply2 nf_abs. 
eapply2 nf_active. 
eapply2 nf_compound. 
eapply2 lift_rec_preserves_normal.
eapply2 nf_compound. 
eapply2 nf_abs. 
eapply2 normal_subst_app_ref. 
eapply2 lift_rec_preserves_normal.
Qed. 


Lemma leastrec_body_normal : forall f, normal f -> normal (leastrec_body f).
Proof. 
split_all. unfold leastrec_body. unfold_op. 
gen_case H f. 
gen_case H l. 
gen_case H l1. 
gen_case H l3. 
gen_case H o. 
eapply2 eager_normal. 
eapply2 wait_normal. 
eapply2 wait_normal. 
eapply2 little_omega_normal. 
eapply2 little_omega_normal. 
eapply2 nf_abs. 
eapply2 nf_abs. 
eapply2 nf_active. 
eapply2 nf_compound. 
eapply2 nf_compound. 
eapply2 nf_active. 
eapply2 nf_compound. 
eapply2 nf_compound. 
eapply2 lift_rec_preserves_normal.
inversion H; split_all. 
inversion H2; split_all. 
inversion H7; split_all. 
inversion H7; split_all. 
inversion H2; split_all. 
inversion H7; split_all. 
inversion H7; split_all. 
eapply2 lift_rec_preserves_normal. 
inversion H; split_all. 
inversion H2; split_all. 
inversion H2; split_all. 
eapply2 lift_rec_preserves_normal. 
inversion H; split_all. 
simpl. 
rewrite lift_rec_preserves_status. 
unfold relocate. 
elim(test 2 (status l4)); split_all. 
omega. 
inversion H. 
simpl in *. auto. 
inversion H4. 

eapply2 nf_compound. 
eapply2 nf_compound. 
eapply2 nf_active. 
split_all. 
simpl.
rewrite lift_rec_preserves_status. 
unfold relocate. 
elim(test 2 (status l4)); split_all. 
omega. 
inversion H. 
simpl in *. auto. 
inversion H4. 
Qed. 



Inductive recbody : nat -> lamSF -> Prop := 
| zero_body  : forall n, recbody n (natrep 0)
| succ_body: forall n, recbody (S n) (App s_op (Ref 0))
| proj_body: forall n i,  recbody (n+i) (Ref i)
| comp_body : forall k (f: lamSF) (gs: list lamSF), recbody (length gs) f -> (forall g, In g gs -> recbody k g) -> recbody k (composition_body f gs)
| prim_body : forall n f g, recbody n f -> recbody (S (S n)) g -> recbody (S n) (primrec_body f g)
| lrec_body : forall n f, recbody (S n) f -> recbody n (leastrec_body f)
.

Lemma recbodies_are_normal : forall n f, recbody n f -> normal f. 
Proof. 
intros n f rb; induction rb; split_all; unfold_op; split_all. 
eapply2 composition_body_normal. 
eapply2 primrec_body_normal. 
eapply2 leastrec_body_normal.
Qed. 


