(** * Series

Authors:
    - Jim Portegies

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
Require Import Lra.
Require Import Classical.
Require Import Classical_Pred_Type.
Require Import ClassicalChoice.

Require Import Waterproof.AllTactics.
Require Import Waterproof.load_database.RealsAndIntegers.
Require Import Waterproof.notations.notations.
Require Import Waterproof.set_search_depth.To_5.
Require Import Waterproof.set_intuition.Disabled.
Require Import Waterproof.load_database.DisableWildcard.

Require Import Waterproof.theory.analysis.sequences.

Global Hint Resolve Rabs_Rabsolu.
Global Hint Resolve Rabs_minus_sym.
Global Hint Resolve Rmult_lt_0_compat : real.
Global Hint Resolve Rinv_lt_contravar : real.

Lemma sigma_split_v2 :
  ∀ (a : ℕ → ℝ) (k l N : ℕ),
    (k < l)%nat ⇒ (l ≤ N)%nat 
      ⇒ sigma a k N = sigma a k (l - 1)%nat + sigma a l N.
Proof.
    Take a : (ℕ → ℝ) and k, l, Nn : ℕ.
    Assume k_lt_N : (k < l)%nat and l_le_N : (l ≤ Nn)%nat.
    It holds that H1 : (l = S (l - 1)%nat ).
    rewrite H1 at 2.
    apply sigma_split with (low := k) (k := (l-1)%nat) (high := Nn).
    This follows immediately.
    This concludes the proof.
Qed.


Notation partial_sums := sum_f_R0.

Lemma partial_sums_pos_incr :
  ∀ (a : ℕ → ℝ), (∀ n : ℕ, a n ≥ 0)⇒
    Un_growing (partial_sums a).
Proof.
    Take a : (ℕ → ℝ).
    Assume terms_pos : (∀ n : ℕ, a n ≥ 0).
    Expand the definition of Un_growing.
    That is, write the goal as (for all n : ℕ,  partial_sums a n ≤ partial_sums a (S n)).
    We need to show that (for all n : ℕ, partial_sums a n ≤ partial_sums a (S n)).
    Take n : ℕ.
    Rewrite using (partial_sums a (S n) = partial_sums a n + a (S n)).
    It holds that H1 : (a (S n) ≥ 0).
    It follows that (partial_sums a n ≤ partial_sums a n + a (S n)).
Qed.


Definition series_cv_to (a : ℕ → ℝ) (l : ℝ) :=
  Un_cv (partial_sums a) l.
Definition series_cv (a : ℕ → ℝ) :=
  ∃ l : ℝ, series_cv_to a l.
Definition series_cv_abs (a : ℕ → ℝ) :=
  series_cv (fun n ↦ Rabs( a n )).
Definition series_cv_abs_to (a : ℕ → ℝ) (l : ℝ) :=
  series_cv_to (fun n ↦ Rabs(a n)) l.


Theorem mouse_tail :
  ∀ (a : ℕ → ℝ) (k l : ℕ) (L : ℝ),
    (k < l)%nat ⇒
      ((Un_cv (fun Nn ↦ sigma a l Nn) L)
        ⇔ 
      (Un_cv (fun Nn ↦ sigma a k Nn) ((sigma a k (l-1)) + L))).
Proof.
    Take a : (ℕ → ℝ) and k, l : ℕ and L : ℝ.
    split.
    Assume sigma_l_cv : (Un_cv (Nn) ↦ (sigma a l Nn) L).
    We claim that H1 : (Un_cv (fun N ↦ sigma a k (l-1)%nat) (sigma a k (l-1)%nat)).
    Apply lim_const_seq.
    By CV_plus it holds that H2 : (Un_cv (fun Nn ↦ sigma a k (l-1)%nat + sigma a l Nn) (sigma a k (l-1)%nat + L)).
    We claim that H3 : (∃ M : ℕ, ∀ n : ℕ, (n ≥ M)%nat ⇒ sigma a k n = sigma a k (l - 1)%nat + sigma a l n).
    Choose M := l%nat.
    Take n : ℕ. 
    Assume n_ge_l : (n ≥ M)%nat.
    Apply sigma_split_v2. 
    This follows by assumption. 
    This follows immediately.
    apply conv_evt_eq_seq with (a := fun Nn ↦ sigma a k (l-1) + sigma a l Nn) (b := fun Nn ↦ sigma a k Nn).
    Choose M such that H5 according to H3.
    Expand the definition of evt_eq_sequences.
    That is, write the goal as (there exists k0 : ℕ, for all n : ℕ, (n ≥ k0)%nat 
      ⇨ sigma a k (l - 1) + sigma a l n = sigma a k n).
    Choose k0 := M.
    Take n : ℕ.
    Assume n_ge_M : (n ≥ M)%nat.
    It holds that H6 : (sigma a k n = sigma a k (l-1) + sigma a l n).
    It holds that H7 : (sigma a k (l-1) + sigma a l n = sigma a k n).
    Apply H7.
    Apply H2.
    Assume sigma_k_cv : (Un_cv (Nn) ↦ (sigma a k Nn) (sigma a k (l - 1) + L)).
    We claim that H7 : (Un_cv (fun N ↦ sigma a k (l-1)) (sigma a k (l-1))).
    Apply lim_const_seq.
    By CV_minus it holds that H8 : (Un_cv (fun N ↦ sigma a k N - (sigma a k (l-1))) (sigma a k (l-1) + L - (sigma a k (l-1)))).
    We claim that H9 : (∃ M : ℕ, ∀ n : ℕ, (n ≥ M)%nat ⇒ sigma a k n - sigma a k (l - 1)%nat = sigma a l n ).
    Choose M := l.
    Take n : ℕ. 
    Assume n_ge_l : (n ≥ l)%nat. 
    By sigma_split_v2 it holds that H10 : (sigma a k n = sigma a k (l - 1)%nat + sigma a l n).
    We need to show that (sigma a k n - sigma a k (l-1) = sigma a l n).
    It follows that (sigma a k n - sigma a k (l - 1) = sigma a l n).
    Rewrite using (L = sigma a k (l-1) + L - sigma a k (l-1)).
    apply conv_evt_eq_seq with (a := fun n ↦ sigma a k n - sigma a k (l-1)) (b := fun n ↦ sigma a l n).
    Choose M such that H11 according to H9.
    Expand the definition of evt_eq_sequences.
    That is, write the goal as (there exists k0 : ℕ, for all n : ℕ, (n ≥ k0)%nat 
      ⇨ sigma a k n - sigma a k (l - 1) = sigma a l n).
    Choose k0 := M.
    Apply H11.
    Apply H8.
Qed.
