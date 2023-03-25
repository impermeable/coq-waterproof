(** * Reals

Authors:
    - Jim Portegies
    - Jelle Wemmenhove
    - Adrian Vramulet (1284487)
    - Tudor Voicu (1339532)
    - Lulof Pirée (1363638)
    - Cosmin Manea (1298542)

Creation date: 25 Mar 2023.

This file derives additional lemmas for the standard library reals.

This file is part of Waterproof-lib.

Waterproof-lib is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

Waterproof-lib is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with Waterproof-lib.  If not, see <https://www.gnu.org/licenses/>.
*)

Require Import Reals.
Require Import Reals.ROrderedType.
Require Import definitions.inequality_chains.
Require Import Waterproof.tactics.simplify_chains.
Require Import Coq.micromega.Lra.

Local Open Scope R_scope.

Lemma Req_true : forall x y : R, x = y -> Reqb x y = true.
Proof.
    intros. 
    destruct (Reqb_eq x y). 
    apply (H1 H).
Qed.

Lemma true_Req : forall x y : R, Reqb x y = true -> x = y.
Proof.
    intros.
    destruct (Reqb_eq x y). 
    apply (H0 H).
Qed.

Lemma Req_false : forall x y : R, x <> y -> Reqb x y = false.
Proof.
    intros. 
    unfold Reqb. 
    destruct Req_dec. 
    contradiction. 
    trivial.
Qed.

Lemma false_Req : forall x y : R, Reqb x y = false -> x <> y.
Proof.
    intros. 
    destruct (Req_dec x y). 
    rewrite (Req_true x y e) in H. 
    assert (H1 : true <> false). 
    auto with *. 
    contradiction.
    apply n.
Qed.

(** ## Lemmas regarding identities for absolute values and inverses*)
Lemma div_sign_flip : forall r1 r2 : R, r1 > 0 -> r2 > 0 -> r1 > 1 / r2 -> 1 / r1 < r2.
Proof.
    intros.
    unfold Rdiv in *.
    rewrite Rmult_1_l in *.
    rewrite <- (Rinv_inv r2).
    apply (Rinv_lt_contravar (/ r2) r1).
    apply Rmult_lt_0_compat. 
    apply Rinv_0_lt_compat. 
    apply H0. 
    apply H.
    apply H1.
Qed.

Lemma div_pos : forall r1 r2 : R, r1 > 0 ->1 / r1 > 0.
Proof.
    intros. 
    unfold Rdiv. 
    rewrite Rmult_1_l. 
    apply Rinv_0_lt_compat. 
    apply H.
Qed.

Lemma Rabs_zero : forall r : R, Rabs (r - 0) = Rabs r.
Proof.
    intros. 
    rewrite Rminus_0_r. 
    trivial.
Qed.

Lemma inv_remove : forall r1 r2 : R, 0 < r1 -> 0 < r2 -> 1 / r1 < 1 / r2 -> r1 > r2.
Proof.
    intros.
    unfold Rdiv in *. 
    rewrite Rmult_1_l in *.
    rewrite <- (Rinv_inv r1), <- (Rinv_inv r2).
    apply (Rinv_lt_contravar (/ r1) (/ r2)). 
    apply Rmult_lt_0_compat. 
    apply Rinv_0_lt_compat. 
    apply H.
    apply Rinv_0_lt_compat. 
    apply H0. 
    rewrite Rmult_1_l in *. 
    apply H1.
    all: apply Rgt_not_eq; assumption.
Qed.

Lemma Rle_abs_min : forall x : R, -x <= Rabs x.
Proof.
    intros. 
    rewrite <- (Rabs_Ropp (x)). 
    apply Rle_abs.
Qed.

Lemma Rge_min_abs : forall x : R, x >= -Rabs x.
Proof.
    intros. 
    rewrite <- (Ropp_involutive x). 
    apply Ropp_le_ge_contravar.
    rewrite (Rabs_Ropp (- x)). 
    apply Rle_abs.
Qed.

Lemma Rmax_abs : forall a b : R, Rmax (Rabs a) (Rabs b) >= 0.
Proof.
    intros.
    apply (Rge_trans _ (Rabs a) _).
    apply Rle_ge.
    apply Rmax_l.
    apply (Rle_ge 0 (Rabs a)).
    apply Rabs_pos.
Qed.

Lemma Rabs_left1_with_minus :
  forall a b : R,
    0 < a -> b = -a -> Rabs (b) = a.
Proof.
  intros a b a_gt_0 b_eq_min_a.
  rewrite b_eq_min_a.
  unfold Rabs.
  destruct (Rcase_abs(-a)).
  - apply Ropp_involutive.
  - assert (- a < 0).
    {
      rewrite<- Ropp_0.
      apply Ropp_lt_contravar.
      assumption.
    }
    pose proof (Rlt_not_ge (-a) 0 H).
    contradiction.
Qed.

(** ## Lemmas for decidability. *)
(** * Reals *)


(** Lemmas to write e.g. `{r1 ≤ r2} + {r2 < r1}`.*)

Lemma Rlt_ge_dec : forall r1 r2, {r1 < r2} + {r1 >= r2}.
Proof.
    intros.
    destruct (total_order_T r1 r2). 
    destruct s.
    exact (left r).
    exact (right (Req_ge r1 r2 e)). 
    exact (right (Rle_ge r2 r1 (Rlt_le r2 r1 r))).
Qed.
Lemma Rle_ge_dec : forall r1 r2, {r1 <= r2} + {~ r2 >= r1}.
Proof.
    intros.
    destruct (total_order_T r1 r2).
    destruct s.
    apply (left (Rlt_le r1 r2 r)).
    apply (left (Req_le r1 r2 e)).
    apply (right (Rlt_not_ge r2 r1 r)).
Qed.
Lemma Rge_le_dec : forall r1 r2, {r1 >= r2} + {~ r2 <= r1}.
Proof.
    intros.
    destruct (total_order_T r1 r2). 
    destruct s.
    apply (right (Rlt_not_le r2 r1 r)).
    apply (left (Req_ge r1 r2 e)).
    apply (left (Rgt_ge r1 r2 r)).
Qed.


(** Lemmas to split e.g. `{r1 <= r2} into {r1 < r2} + {r1 = r2}`.*)
Lemma Rge_lt_or_eq_dec : forall r1 r2, (r1 >= r2) -> {r2 < r1} + {r1 = r2}.
Proof.
    intros.
    destruct (total_order_T r2 r1).
    - destruct s.
      + left. exact r.
      + right. symmetry. exact e.
    - exfalso.
      exact (Rlt_not_ge _ _ r H).
Qed.

Close Scope R_scope.

(** ** Populate the Waterproof reals database *)

Global Hint Extern 3 ( @eq R _ _ ) => ltac2:(simpl_ineq_chains ()); field : reals.

Global Hint Extern 3 ( Rle _ _ ) => cbn; ltac2:(simpl_ineq_chains ()); lra : reals.
Global Hint Extern 3 ( Rge _ _ ) => cbn; ltac2:(simpl_ineq_chains ()); lra : reals.
Global Hint Extern 3 ( Rlt _ _ ) => cbn; ltac2:(simpl_ineq_chains ()); lra : reals.
Global Hint Extern 3 ( Rgt _ _ ) => cbn; ltac2:(simpl_ineq_chains ()); lra : reals.

Global Hint Extern 3 (~ (Rle _ _) ) => cbn; ltac2:(simpl_ineq_chains ()); lra : reals.
Global Hint Extern 3 (~ (Rge _ _) ) => cbn; ltac2:(simpl_ineq_chains ()); lra : reals.
Global Hint Extern 3 (~ (Rlt _ _) ) => cbn; ltac2:(simpl_ineq_chains ()); lra : reals.
Global Hint Extern 3 (~ (Rgt _ _) ) => cbn; ltac2:(simpl_ineq_chains ()); lra : reals.
Global Hint Extern 3 (~ (@eq R _ _ ) ) => cbn; ltac2:(simpl_ineq_chains ()); lra : reals.

Global Hint Extern 3 ( Rle _ _ ) => cbn; nra : reals.
Global Hint Extern 3 ( Rge _ _ ) => cbn; nra : reals.
Global Hint Extern 3 ( Rlt _ _ ) => cbn; nra : reals.
Global Hint Extern 3 ( Rgt _ _ ) => cbn; nra : reals.

Global Hint Resolve eq_sym : reals.
Global Hint Resolve false_Req : reals.
Global Hint Resolve true_Req : reals.

Global Hint Resolve Rmin_l : reals.
Global Hint Resolve Rmin_r : reals.
Global Hint Resolve Rmax_l : reals.
Global Hint Resolve Rmax_r : reals.
Global Hint Resolve Rle_max_compat_l : reals.
Global Hint Resolve Rle_max_compat_r : reals.
Global Hint Resolve Rmax_lub : reals.
Global Hint Resolve Rmax_lub_lt : reals.
Global Hint Resolve Rmax_left : reals.
Global Hint Resolve Rmax_right : reals.
Global Hint Resolve Rmin_left : reals.
Global Hint Resolve Rmin_right : reals.
Global Hint Resolve Rmin_glb : reals.
Global Hint Resolve Rmin_glb_lt : reals.

Global Hint Resolve div_sign_flip : reals.
Global Hint Resolve div_pos : reals.
Global Hint Resolve inv_remove : reals.
Global Hint Resolve Rinv_inv : reals.
Global Hint Resolve Rabs_def1 : reals.
Global Hint Resolve Rabs_le : reals.
Global Hint Resolve Rabs_left : reals.
Global Hint Resolve Rabs_right : reals.
Global Hint Resolve Rabs_left1 : reals.
Global Hint Resolve Rabs_left1_with_minus : reals.
Global Hint Resolve Rabs_pos_lt : reals.
Global Hint Resolve Rabs_zero : reals.
Global Hint Resolve Rle_abs : reals.
Global Hint Resolve Rabs_pos : reals.
Global Hint Resolve Rle_abs_min : reals.
Global Hint Resolve Rge_min_abs : reals.
Global Hint Resolve Rmax_abs : reals.
Global Hint Resolve Rinv_0_lt_compat : reals.

Global Hint Extern 1 => rewrite Rabs_zero : reals.

(** ** Add hints to decidability database *)

(** Automatically unfold > to <so (_ > _) no longer has to occur in the options below.
    We cannot do the same for >= as it is not defined as <= .*)
Global Hint Extern 1 => unfold Rgt : decidability_reals.

Global Hint Resolve Req_EM_T : decidability_reals.
Global Hint Resolve Rlt_le_dec : decidability_reals.
Global Hint Resolve Rlt_ge_dec : decidability_reals.

(** Lemmas to write e.g. `{r1 ≤ r2} + {~r2 ≥ r1}`.*)
Global Hint Resolve Rlt_dec Rle_dec Rge_dec : decidability_reals.
Global Hint Resolve Rle_ge_dec Rge_le_dec : decidability_reals.
Global Hint Resolve Rle_lt_or_eq_dec Rge_lt_or_eq_dec : decidability_reals.

Global Hint Resolve total_order_T : decidability_reals. (* x < y, x = y or y < x*)

