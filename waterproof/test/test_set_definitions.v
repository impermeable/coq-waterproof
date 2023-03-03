(** * Testcases for [set_definitions.v]
Authors: 
    - Jelle Wemmenhove
Creation date: 21 Oct 2021

Testcases for the definitions of subsets of the reals [R], 
and defintions and tests for subsets of a general but fixed set [X].
Tests pass if they can be run without unhandled errors.
--------------------------------------------------------------------------------

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
Require Import Waterproof.definitions.set_definitions.
Require Import Waterproof.notations.notations.
Require Import Reals.
Require Import Lra.
Open Scope R_scope.
Open Scope subset_scope.

Local Parameter P : R -> Prop.
Definition A := as_subset R P.

Local Parameter x : R.
Definition type_check_1 : Prop := (x : A).
Definition type_check_2 : (R -> Prop) := is_lub A.
Definition type_check_3 : Prop :=  (x : [0,1]).

Goal is_upper_bound [0,1] 1.
Proof.
  unfold is_upper_bound.
  intro a.
  intro a_in_interval.
  assert (0 <= a <= 1) by auto.
  lra.
Qed.

Goal 1/2 : [0,1].
Proof.
  enough (0 <= 1/2 <= 1) by auto.
  lra.
Qed.