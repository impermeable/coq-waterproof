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

Require Import Notations.Common.
Require Import Notations.Reals.
Require Import Notations.Sets.
Require Import Chains.
Require Import Tactics.
Require Import Waterproof.Automation.

Waterproof Enable Automation RealsAndIntegers.
Waterproof Enable Automation Intuition.

Open Scope R_scope.

(** Definitions *)
Definition is_accumulation_point (a : R) :=
  ∀ ε > 0, ∃ x ∈ R, 0 < |x - a| < ε.

Definition is_isolated_point (a : R) :=
  ∃ ε > 0, ∀ x ∈ R, |x - a| = 0 ∨ (ε ≤ |x - a|).

Definition limit_in_point (f : R → R) (a : R) (q : R) :=
 ∀ ε > 0, ∃ δ > 0, ∀ x ∈ R, (0 < |x - a| < δ) ⇒ (|(f x) - q| < ε).

Definition is_continuous_in (f : R → R) (a : R) :=
  ((is_accumulation_point a) ∧ (limit_in_point f a (f a))) ∨ (is_isolated_point a).

Lemma every_point_in_R_acc_point_R (a : R) :
  is_accumulation_point a.
Proof.
  We need to show that (∀ r > 0, ∃ x ∈ R, 0 < | x - a | < r).
  Take r > 0.
  Choose x := (a + r/2).
  * Indeed, (x ∈ ℝ).
  * We need to show that (0 < | x - a | < r).
    unfold gt_op, R_gt_type in *.
    It holds that (| x - a | < r).
    It holds that (| x - a | > 0).
    We conclude that (0 < | x - a | < r).
Qed.

Theorem alt_char_continuity (h : R → R) (a : R) :
    is_continuous_in h a ⇔ ∀ ε > 0, ∃ δ > 0,
      (∀ x ∈ R, 0 < | x - a | < δ ⇒ | h(x) - h(a) | < ε).
Proof.
  We show both directions.
  * We need to show that (is_continuous_in(h, a) ⇨ ∀ ε > 0, ∃ δ > 0, ∀ x ∈ ℝ,
      0 < |x - a| < δ ⇨ |h(x) - h(a)| < ε).
    Assume that (is_continuous_in h a).
    Either ((is_accumulation_point a) ∧ (limit_in_point h a (h a))) or (is_isolated_point a).
    + Case ((is_accumulation_point a) ∧ (limit_in_point h a (h a))).
      Take ε > 0.
      It holds that (∃ δ1 > 0, ∀ x ∈ R,
          (0 < |x - a| < δ1) ⇒ (|(h x) - (h a)| < ε)).
      Obtain such a δ1.
      Choose δ := (δ1).
      - Indeed, (δ > 0).
      - We conclude that (∀ x ∈ ℝ,
          0 < |x - a| < δ ⇨ |h(x) - h(a)| < ε).
    + Case (is_isolated_point a).
      It holds that (∃ ε > 0, ∀ x ∈ ℝ, |x - a| = 0 ∨ ε ≤ |x - a|).
      Obtain such an ε.
      It holds that (ε > 0).
      Define z := (a + ε / 2).
      It holds that (|z - a| = 0 \/ ε ≤ | z - a |) (ii).
      destruct ii.
      - It holds that (| z - a | > 0).
        Contradiction.
      - It holds that (| z - a| < ε).
        Contradiction.
  * We need to show that ((∀ ε > 0, ∃ δ > 0, ∀ x ∈ ℝ,
      0 < |x - a| < δ ⇨ |h(x) - h(a)| < ε) ⇨ is_continuous_in(h, a)).
    Assume that (∀ ε > 0, ∃ δ > 0, ∀ x ∈ ℝ,
 0 < |x - a| < δ ⇨ |h(x) - h(a)| < ε) .
    unfold is_continuous_in.
    We need to show that (is_accumulation_point(a) ∧ limit_in_point(h, a, h(a)) ∨ is_isolated_point(a)).
    It suffices to show that (is_accumulation_point(a) ∧ limit_in_point(h, a, h(a)) ).
    We show both statements.
    + By (every_point_in_R_acc_point_R) we conclude that (is_accumulation_point a).
    + We conclude that (limit_in_point(h, a, h a)).
Qed.

#[export] Hint Resolve -> alt_char_continuity : wp_reals.
#[export] Hint Resolve <- alt_char_continuity : wp_reals.

(** Notations *)
Notation "a 'is' 'an' '_accumulation' 'point_'" := (is_accumulation_point a) (at level 69).

Notation "a 'is' 'an' 'accumulation' 'point'" := (is_accumulation_point a) (at level 69, only parsing).

Local Ltac2 unfold_acc_point (statement : constr) := eval unfold is_accumulation_point in $statement.
Ltac2 Notation "Expand" "the" "definition" "of" "accumulation" "point" x(opt(seq("in", constr))) :=
  wp_unfold unfold_acc_point (Some "accumulation point") true x.
Ltac2 Notation "_internal_" "Expand" "the" "definition" "of" "accumulation" "point" x(opt(seq("in", constr))) :=
  wp_unfold unfold_acc_point (Some "accumulation point") false x.


Notation "a 'is' 'an' '_isolated' 'point_'" := (is_isolated_point a) (at level 69).

Notation "a 'is' 'an' 'isolated' 'point'" := (is_isolated_point a) (at level 69, only parsing).

Local Ltac2 unfold_isol_point (statement : constr) := eval unfold is_isolated_point in $statement.

Ltac2 Notation "Expand" "the" "definition" "of" "isolated" "point" x(opt(seq("in", constr))) :=
  wp_unfold unfold_isol_point (Some "isolated point") true x.
Ltac2 Notation "_internal_" "Expand" "the" "definition" "of" "isolated" "point" x(opt(seq("in", constr))) :=
  wp_unfold unfold_isol_point (Some "isolated point") false x.

Notation "'_limit_' 'of' f 'in' a 'is' L" := (limit_in_point f a L) (at level 69).

Notation "'limit' 'of' f 'in' a 'is' L" := (limit_in_point f a L) (at level 69, only parsing).

Local Ltac2 unfold_lim_in_point (statement : constr) := eval unfold limit_in_point in $statement.

Ltac2 Notation "Expand" "the" "definition" "of" "limit" x(opt(seq("in", constr))) :=
  wp_unfold unfold_lim_in_point (Some "limit") true x.
Ltac2 Notation "_internal_" "Expand" "the" "definition" "of" "limit" x(opt(seq("in", constr))) :=
  wp_unfold unfold_lim_in_point (Some "limit") false x.


Notation "f 'is' '_continuous_' 'in' a" := (is_continuous_in f a) (at level 69).

Notation "f 'is' 'continuous' 'in' a" := (is_continuous_in f a)  (at level 69, only parsing).

Local Ltac2 unfold_is_cont (statement : constr) := eval unfold is_continuous_in in $statement.

Ltac2 Notation "Expand" "the" "definition" "of" "continuous" x(opt(seq("in", constr))) :=
  wp_unfold unfold_is_cont (Some "continuous") true x.
Ltac2 Notation "_internal_" "Expand" "the" "definition" "of" "continuous" x(opt(seq("in", constr))) :=
  wp_unfold unfold_is_cont (Some "continuous") false x.

Close Scope R_scope.
