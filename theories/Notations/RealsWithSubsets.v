Require Import Stdlib.Reals.Reals.

Require Import Waterproof.Notations.Common.
Require Import Waterproof.Notations.Sets.
Require Import Waterproof.Notations.Reals.

Require Import Waterproof.Libs.Reals.

Declare Scope R2_scope.

Notation "'ℤ'" := Z_in_R : R2_scope.
Notation "'ℚ'" := Q_in_R : R2_scope.

Open Scope R_scope.
Open Scope subset_scope.
Open Scope R2_scope.

Notation "q 'is' 'rational'" := (is_rational q) (at level 1) : R2_scope.

Notation "q 'is' 'irrational'" := (¬(q is rational)) (at level 1) : R2_scope.

Notation " A 'is' 'a' 'single' 'interval'" := (is_interval A) (at level 1) : R_scope.
