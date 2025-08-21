
Require Import Waterproof.Notations.Common.
Require Import Waterproof.Notations.Sets.
Require Import Waterproof.Notations.Reals.
Require Import Waterproof.Notations.RealsWithSubsets.

Require Import Coq.Reals.Reals.

Require Import Waterproof.Libs.Reals.Integer.
Require Import Waterproof.Libs.Reals.Rational.
Require Import Waterproof.Libs.Reals.RealInequalities.

Require Import Waterproof.Waterproof.
Require Import Waterproof.Tactics.
Require Import Waterproof.Automation.

Open Scope R_scope.
Open Scope subset_scope.
Open Scope R2_scope.

Set Default Timeout 10.

Waterproof Enable Automation RealsAndIntegers.

Lemma exercise_irrational_negation (x : ℝ) : x is irrational ⇒ (-x) is irrational.
Proof.
Assume that x is irrational.
Assume that (-x) is rational.
It holds that ∃ a ∈ ℤ, ∃ b ∈ ℤ, 0 ≠ b ∧ (-x) = a/b.
Obtain such an a, b.
It holds that 0 ≠ b ∧ (-x) = a/b.
It holds that b ≠ 0.
It holds that x = (-a)/b.
It holds that x is rational.
Contradiction.
Qed.

