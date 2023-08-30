(******************************************************************************)
(*                  This file is part of Waterproof-lib.                      *)
(*                                                                            *)
(*   Waterproof-lib is free software: you can redistribute it and/or modify   *)
(*    it under the terms of the GNU General Public License as published by    *)
(*     the Free Software Foundation, either version 3 of the License, or      *)
(*                    (at your option) any later version.                     *)
(*                                                                            *)
(*     Waterproof-lib is distributed in the hope that it will be useful,      *)
(*      but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*       MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the         *)
(*               GNU General Public License for more details.                 *)
(*                                                                            *)
(*     You should have received a copy of the GNU General Public License      *)
(*   along with Waterproof-lib. If not, see <https://www.gnu.org/licenses/>.  *)
(*                                                                            *)
(******************************************************************************)

Require Import Lra.
Require Import Coq.Reals.Reals.
Require Import Reals.ROrderedType.

Require Import Notations.

Local Open Scope R_scope.

(** * Lemmas linking reals and booleans *)

Lemma Req_true : forall x y : R, x = y -> Reqb x y = true.
Proof.
  intros x y H.
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

(** * Lemmas regarding identities for absolute values and inverses *)

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
  forall a b : R, 0 < a -> b = -a -> Rabs (b) = a.
Proof.
  intros a b a_gt_0 b_eq_min_a.
  rewrite b_eq_min_a.
  unfold Rabs.
  destruct (Rcase_abs(-a)).
  - apply Ropp_involutive.
  - assert (- a < 0).
    + rewrite<- Ropp_0.
      apply Ropp_lt_contravar.
      assumption.
    + pose proof (Rlt_not_ge (-a) 0 H).
      contradiction.
Qed.

(** * Lemmas for decidability *)

(** ** Lemmas to write e.g. <<{r1 ≤ r2} + {r2 < r1}>> *)

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


(** ** Lemmas to split e.g. <<{r1 <= r2}>> into <<{r1 < r2} + {r1 = r2}>> *)

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

Open Scope subset_scope.

Lemma left_in_closed_open {a b : R} : (a < b) -> (a : [a,b)).
Proof.
  intro a_lt_b.
  split.
  - apply Rle_refl.
  - exact a_lt_b.
Qed.

Lemma right_in_open_closed {a b : R} : (a < b) -> (b : (a,b]).
Proof.
  intro a_lt_b.
  split.
  - exact a_lt_b.
  - apply Rle_refl.
Qed.
Close Scope subset_scope.

Close Scope R_scope.

Require Import Ltac2.Ltac2.

(** Tactic to deal with Rabs Rmin Rmax *)

Ltac2 crush_R_abs_min_max () := 
  unfold Rdist in *;
  unfold Rabs in *;
  unfold Rmax in *;
  unfold Rmin in *; 
  repeat (destruct (Rcase_abs) in * );
  repeat (destruct (Rle_dec) in * );
  repeat (destruct (Rge_dec) in * ).
