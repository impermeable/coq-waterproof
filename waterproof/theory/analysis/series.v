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
    Take a : (ℕ → ℝ) and k, l, Nn : ℕ; such that
      (k < l)%nat and (l ≤ Nn)%nat.
    It holds that H1 : (l = S (l - 1)%nat).
    (* TODO: It suffices to show that (sigma a k Nn = sigma a k (l - 1) + sigma a (S (l - 1)) Nn).*)
    rewrite H1 at 2.
    By sigma_split it suffices to show that (k <= l - 1 < Nn)%nat.
    We show both (k <= l - 1)%nat and (l - 1 < Nn)%nat.
    - We conclude that (k ≤ l - 1)%nat.
    - We conclude that (l - 1 < Nn)%nat.
Qed.


Notation partial_sums := sum_f_R0.

Lemma partial_sums_pos_incr :
  ∀ (a : ℕ → ℝ), (∀ n : ℕ, a n ≥ 0)⇒
    Un_growing (partial_sums a).
Proof.
    Take a : (ℕ → ℝ); such that (∀ n : ℕ, a n ≥ 0).
    Expand the definition of Un_growing.
    That is, write the goal as (for all n : ℕ,  partial_sums a n ≤ partial_sums a (S n)).
    We need to show that (for all n : ℕ, partial_sums a n ≤ partial_sums a (S n)).
    Take n : ℕ.
    It holds that H1 : (a (S n) ≥ 0).
    It holds that H2 : ((partial_sums a n) + a (S n) = partial_sums a (S n)).
    We conclude that (& partial_sums a n &<= (partial_sums a n) + a (S n) 
                                         &= partial_sums a (S n)).
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
    Assume that (k < l)%nat.
    We show both directions.
    - We need to show that (Un_cv (Nn) ↦ (sigma a l Nn) L
        ⇨ Un_cv (Nn) ↦ (sigma a k Nn) (sigma a k (l - 1) + L)).
      Assume (Un_cv (Nn) ↦ (sigma a l Nn) L).
      (* TODO: fix
         By lim_const_seq it holds that H1 : (Un_cv (fun N ↦ sigma a k (l-1)%nat) (sigma a k (l-1)%nat)). *)
      We claim that H1 : (Un_cv (fun N ↦ sigma a k (l-1)) (sigma a k (l-1))).
      { We need to show that ((constant_sequence (sigma a k (l-1))) ⟶ (sigma a k (l-1))).
        By lim_const_seq we conclude that (constant_sequence (sigma a k (l-1)) ⟶ sigma a k (l-1)).
      }
      By CV_plus it holds that H2 : (Un_cv (fun Nn ↦ sigma a k (l-1)%nat + sigma a l Nn) (sigma a k (l-1)%nat + L)).
      We claim that H3 : (evt_eq_sequences (Nn ↦ (sigma a k (l - 1) + sigma a l Nn)) (Nn ↦ (sigma a k Nn))).
      { We need to show that (∃ M : ℕ, ∀ n : ℕ, (n ≥ M)%nat ⇒ sigma a k (l - 1)%nat + sigma a l n = sigma a k n).
        Choose M := l%nat.
        Take n : ℕ; such that (n ≥ M)%nat.
        By sigma_split_v2 it suffices to show that (k < l <= n)%nat.
        We conclude that (k < l <= n)%nat.
      }
      (* TODO: find way of dealing with the case when coq cannot find parameters for apply ...*)
      apply conv_evt_eq_seq with (a := fun Nn ↦ sigma a k (l-1) + sigma a l Nn).
      + We conclude that (evt_eq_sequences (Nn) ↦ (sigma a k (l - 1) + sigma a l Nn) (Nn) ↦ (sigma a k Nn)).
      + (*TODO: fix  We conclude that ((Nn) ↦ (sigma a k (l - 1) + sigma a l Nn)). *)   
        We need to show that (Un_cv (Nn) ↦ (sigma a k (l - 1) + sigma a l Nn) (sigma a k (l - 1) + L)).
        We conclude that (Un_cv (Nn) ↦ (sigma a k (l - 1) + sigma a l Nn) (sigma a k (l - 1) + L)).
    - We need to show that (Un_cv (Nn) ↦ (sigma a k Nn) (sigma a k (l - 1) + L) ⇨ Un_cv (Nn) ↦ (sigma a l Nn) L).
      Assume that (Un_cv (Nn) ↦ (sigma a k Nn) (sigma a k (l - 1) + L)).
      We claim that H1 : (Un_cv (fun N ↦ sigma a k (l-1)) (sigma a k (l-1))).
      { We need to show that ((constant_sequence (sigma a k (l-1))) ⟶ (sigma a k (l-1))).
        By lim_const_seq we conclude that (constant_sequence (sigma a k (l-1)) ⟶ sigma a k (l-1)).
      }
      By CV_minus it holds that H2 : (Un_cv (fun N ↦ sigma a k N - (sigma a k (l-1))) (sigma a k (l-1) + L - (sigma a k (l-1)))).
      We claim that H3 : (evt_eq_sequences (Nn ↦ (sigma a k Nn - sigma a k (l-1))) (Nn ↦ (sigma a l Nn))).
      { We need to show that (∃ M : ℕ, ∀ n : ℕ, (n ≥ M)%nat ⇒ sigma a k n - sigma a k (l-1) = sigma a l n).
        Choose M := l%nat.
        Take n : ℕ; such that (n ≥ M)%nat.
        It suffices to show that (sigma a k n = sigma a k (l - 1) + sigma a l n).
        By sigma_split_v2 it suffices to show that (k < l <= n)%nat.
        We conclude that (k < l <= n)%nat.
      }
      apply conv_evt_eq_seq with (a := fun n ↦ sigma a k n - sigma a k (l-1)) (b := fun n ↦ sigma a l n).
      + We conclude that (evt_eq_sequences (n) ↦ (sigma a k n - sigma a k (l - 1)) (n) ↦ (sigma a l n)).
      + We need to show that (Un_cv (N) ↦ (sigma a k N - sigma a k (l - 1)) L).
        It holds that H4 : ((sigma a k (l - 1) + L - sigma a k (l - 1)) = L).
        (* It suffices to show that (Un_cv (N) ↦ (sigma a k N - sigma a k (l - 1)) (sigma a k (l - 1) + L - sigma a k (l - 1))).*)
        rewrite <- H4. (* TODO come up with some notation for this (meaning transport)*)
        We conclude that (Un_cv (N) ↦ (sigma a k N - sigma a k (l - 1)) (sigma a k (l - 1) + L - sigma a k (l - 1))).
Qed.
