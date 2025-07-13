Require Import Coq.Reals.Reals.

Require Import Notations.Common.
Require Import Notations.Sets.
Require Import Notations.Reals.

Require Import Libs.Reals.

Declare Scope R2_scope.

Notation "'ℤ'" := Z_in_R : R2_scope.
Notation "'ℚ'" := Q_in_R : R2_scope.

Open Scope R_scope.
Open Scope subset_scope.
Open Scope R2_scope.

Definition is_rational (q : ℝ) : Prop := ∃n ∈ ℤ, ∃m ∈ ℤ, 0 ≠ m ∧ q = n/m.

Notation "q 'is' 'rational'" := (is_rational q) (at level 70) : R2_scope.

Notation " A 'is' 'a' 'single' 'interval'" := (is_interval A) (at level 70) : R_scope.