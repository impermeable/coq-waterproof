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

Require Import Coq.Reals.Reals.

Require Import Automation.
Require Import Libs.Negation.
Require Import Notations.
Require Import Tactics.

Waterproof Enable Automation RealsAndIntegers.

Open Scope R_scope.

(** Hints *)
Lemma aux1 : for all n m : ℕ, (n = m) ⇒ |m - n| = |n - n|.
Proof.
  Take n, m : ℕ.
  Assume that (n = m).
  We conclude that (& |m - n| = |m - m| = m - m = 0 = n - n = |n - n|).
Qed.
#[export] Hint Resolve aux1 : wp_reals.

(** Useful lemma *)
Lemma useful_lemma : for all n m : ℕ, (n ≠ m) ⇒ (1 ≤ | m - n |).
Proof.
  Take n, m : ℕ. Assume that (n ≠ m).
  assert (n > m ∨ n < m)%nat as i by (apply Nat.lt_gt_cases; auto).
  Because (i) either (n > m)%nat or (n < m)%nat holds.
  + Case (n > m)%nat.
    It holds that (n ≥ S m)%nat.
    By S_INR it holds that (m + 1 = S m).
    It holds that (m + 1 - m = S m - m).
    It holds that ((S m) ≤ n).
    It holds that ((S m) - m ≤ n - m).
    We conclude that
        (& 1 = m + 1 - m = (S m) - m ≤ n - m = | n - m | = | m - n | ).
  + Case (n < m)%nat.
    It holds that (S n ≤ m)%nat.
    By S_INR it holds that (n + 1 = S n).
    It holds that (n + 1 - n = S n - n).
    It holds that ((S n) ≤ m).
    It holds that ((S n) - n ≤ m - n).
    We conclude that (& 1 = n + 1 - n = (S n) - n ≤ m - n = |m - n|).
Qed.

(** Definitions *)
Section metricspace.
Variable X : Metric_Space.
Coercion Base : Metric_Space >-> Sortclass.

Definition is_accumulation_point (a : R) :=
  for all ε : R, (ε > 0) ⇒
    there exists n : nat, 0 < | n - a | < ε.

Definition is_isolated_point (a : R) :=
  there exists ε : R, (ε > 0) ∧
    (for all n : nat, |n - a| = 0 ∨ (ε ≤ |n - a|)).

Definition limit_in_point (f : ℕ → X) (a : ℕ) (L : X) :=
 for all ε : R, (ε > 0) ⇒
   there exists δ : R, (δ > 0) ∧
     (for all n : nat,
       (0 < |n - a| < δ) ⇒ (dist X (f n) L < ε)).

Definition is_continuous_in (f : ℕ → X) (a : ℕ) :=
  ((is_accumulation_point a) ∧ (limit_in_point f a (f a))) ∨ (is_isolated_point a).

Theorem alt_char_continuity :
  ∀ f : ℕ → X, ∀ a : ℕ, 
    is_continuous_in f a ⇔ ∀ ε : R, ε > 0 ⇒ ∃ δ : R, (δ > 0) ∧ (∀ x : ℕ, 0 < | x - a | < δ ⇒ dist X (f(x)) (f(a)) < ε).
Proof.
  Take h : (ℕ → X).
  Take a : ℕ.
  We show both directions.
  * We need to show that (is_continuous_in(h, a) ⇨ for all ε : ℝ,
        ε > 0 ⇨ there exists δ : ℝ,
          δ > 0 ∧ (for all x : ℕ,
            0 < |x - a| < δ ⇨ dist(X, h(x), h(a)) < ε)).
    Assume that (is_continuous_in h a).
    Take ε : R.
    Assume that (ε > 0).
    Choose δ := (1/2).
    We show both statements.
    - We conclude that (δ > 0).
    - We need to show that (for all x : nat,
          0 < |x - a| < δ ⇨ dist(X, h(x), h(a)) < ε).
      Take x : nat.
      Assume that (0 < | x - a | < δ).
      Either (x = a) or (~(x=a)).
      + Case (x = a).
        It holds that (| x - a | = 0).
        Contradiction.
      + Case (~(x = a)).
        By useful_lemma it holds that (1 ≤ | x - a |).
        Contradiction.
  * We need to show that ((for all ε : ℝ,
      ε > 0 ⇨ there exists δ : ℝ,
        δ > 0 ∧ (for all x : ℕ,
          0 < |x - a| < δ ⇨ dist(X, h(x), h(a)) < ε)) ⇨ is_continuous_in(h, a)).
    Assume that ((for all ε : ℝ,
      ε > 0 ⇨ there exists δ : ℝ,
        δ > 0 ∧ (for all x : ℕ,
          0 < |x - a| < δ ⇨ dist(X, h(x), h(a)) < ε))).
    We need to show that (is_accumulation_point(a) ∧ limit_in_point(h, a, h(a)) ∨ is_isolated_point(a)).
    It suffices to show that (is_isolated_point a).
    unfold is_isolated_point.
    We need to show that (∃ ε : ℝ, ε > 0 ∧ (for all n : ℕ, |n - a| = 0 ∨ ε ≤ |n - a|)).
    Choose ε := (1/2).
    We show both statements.
    - We conclude that (ε > 0).
    - We need to show that (for all n : ℕ, |n - a| = 0 ∨ ε ≤ |n - a|).
      Take n : nat.
      Either (n = a) or (~(n=a)).
      + Case (n = a).
        It suffices to show that (|n - a| = 0).
        We conclude that (|n - a| = 0).
      + Case (~(n=a)).
        It suffices to show that ((1/2) ≤ | n - a |).
        By useful_lemma it holds that (1 ≤ | n - a |).
        We conclude that (1/2 ≤ | n - a | ).
Qed.

End metricspace.

(** Notations *)
Notation "a 'is' 'an' '_accumulation' 'point_'" := (is_accumulation_point a) (at level 68).

Notation "a 'is' 'an' 'accumulation' 'point'" := (is_accumulation_point a) (at level 68, only parsing).

Local Ltac2 unfold_acc_point (statement : constr) := eval unfold is_accumulation_point in $statement.
Ltac2 Notation "Expand" "the" "definition" "of" "accumulation" "point" "in" statement(constr) := 
  unfold_in_statement unfold_acc_point (Some "accumulation point") statement.
Ltac2 Notation "_internal_" "Expand" "the" "definition" "of" "accumulation" "point" "in" statement(constr) := 
  unfold_in_statement_no_error unfold_acc_point (Some "accumulation point") statement.

Notation "a 'is' 'an' '_isolated' 'point_'" := (is_isolated_point a) (at level 68).

Notation "a 'is' 'an' 'isolated' 'point'" := (is_isolated_point a) (at level 68, only parsing).

Local Ltac2 unfold_isol_point (statement : constr) := eval unfold is_isolated_point in $statement.

Ltac2 Notation "Expand" "the" "definition" "of" "isolated" "point" "in" statement(constr) := 
  unfold_in_statement unfold_isol_point (Some "isolated point") statement.
Ltac2 Notation "_internal_" "Expand" "the" "definition" "of" "isolated" "point" "in" statement(constr) := 
  unfold_in_statement_no_error unfold_isol_point (Some "isolated point") statement.

Notation "'_limit_' 'of' f 'in' a 'is' L" := (limit_in_point _ f a L) (at level 68).

Notation "'limit' 'of' f 'in' a 'is' L" := (limit_in_point _ f a L) (at level 68, only parsing).

Local Ltac2 unfold_lim_in_point (statement : constr) := eval unfold limit_in_point in $statement.

Ltac2 Notation "Expand" "the" "definition" "of" "limit" "in" statement(constr) := 
  unfold_in_statement unfold_lim_in_point (Some "limit") statement.
Ltac2 Notation "_internal_" "Expand" "the" "definition" "of" "limit" "in" statement(constr) := 
  unfold_in_statement_no_error unfold_lim_in_point (Some "limit") statement.


Notation "f 'is' '_continuous_' 'in' a" := (is_continuous_in _ f a) (at level 68).

Notation "f 'is' 'continuous' 'in' a" := (is_continuous_in _ f a)  (at level 68, only parsing).

Local Ltac2 unfold_is_cont (statement : constr) := eval unfold is_continuous_in in $statement.

Ltac2 Notation "Expand" "the" "definition" "of" "continuous" "in" statement(constr) := 
  unfold_in_statement unfold_is_cont (Some "continuous") statement.
Ltac2 Notation "_internal_" "Expand" "the" "definition" "of" "continuous" "in" statement(constr) := 
  unfold_in_statement_no_error unfold_is_cont (Some "continuous") statement.


Close Scope R_scope.
