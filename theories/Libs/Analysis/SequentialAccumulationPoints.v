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

From Stdlib Require Import Reals.Reals.
From Stdlib Require Import Lra.
From Stdlib Require Import Classical.
From Stdlib Require Import Classical_Pred_Type.
From Stdlib Require Import ClassicalChoice.

Require Import Automation.
Require Import Libs.Analysis.Sequences.
Require Import Libs.Analysis.Subsequences.
Require Import Notations.Common.
Require Import Notations.Reals.
Require Import Notations.Sets.
Require Import Chains.
Require Import Tactics.

Waterproof Enable Automation RealsAndIntegers.

Open Scope R_scope.

Definition is_seq_acc_pt (a : ℕ → ℝ) (x : ℝ) : Prop :=
  ∃ n : ℕ → ℕ, is_index_seq n ∧ converges_to (fun (k : ℕ) ↦ a(n k)) x.

Lemma seq_bdd_seq_acc_pts_bdd (a : ℕ → ℝ) :
  has_ub a ⇒ bound (is_seq_acc_pt a).
Proof.
  Assume that (has_ub a) (i).
  We need to show that
    (there exists m : ℝ, is_upper_bound (is_seq_acc_pt a) m).
  We need to show that (there exists m : ℝ,
    for all x : ℝ, is_seq_acc_pt a x ⇨ x ≤ m).
  By (i) it holds that (there exists M : R, is_upper_bound (EUn a) M).
  Obtain such an M. It holds that (is_upper_bound (EUn a) M).
  Choose m := M.
  Take x : ℝ.
  Assume that (is_seq_acc_pt a x).
  It holds that (∃ n : ℕ ⇨ ℕ,
    is_index_seq n ∧ converges_to (fun k ↦ a(n(k)), x)).
  Obtain such an n.
  It holds that (is_index_seq n ∧ converges_to (fun k ↦ a(n(k)), x)) (iv).
  Because (iv) both (is_index_seq n) and (converges_to (fun k ↦ (a(n(k))), x)) hold.
  We need to show that (x ≤ M).
  (*FIXME*)
  (* By (upp_bd_seq_is_upp_bd_lim (fun k => a (n k))) it suffices to show that
    (∀ k ∈ nat, (a (n k) <= M)).*)
  enough (∀ k ∈ nat, (a (n k) <= M)) by (
  apply (upp_bd_seq_is_upp_bd_lim (fun k ↦ a (n k))); assumption).
  We claim that (for all k : ℕ, (a k) ≤ M) (v).
  { It holds that (for all x0 : ℝ, EUn a x0 ⇨ x0 ≤ M).
    It holds that (for all x0 : ℝ,
      (there exists k : ℕ, x0 = a k) ⇨ x0 ≤ M).
    Take k : ℕ.
    It suffices to show that (there exists k0 : nat, a k = a k0).
    Choose k0 := k.
    We conclude that (a k = a k0).
  }
  Take k ∈ ℕ.
  By (v) it holds that (a(n k) ≤ M).
  It follows that (a(n k) ≤ M).
Qed.

Close Scope R_scope.
