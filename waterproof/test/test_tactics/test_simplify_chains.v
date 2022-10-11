(** * Testcases for [take.v]
Authors: 
    - Jim Portegies
Creation date: 31 Oct 2021

Testcases for the [simplify_chains] tactic.
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

From Ltac2 Require Import Ltac2.
From Ltac2 Require Option.
From Ltac2 Require Import Message.

Require Import Waterproof.test_auxiliary.
Require Import Waterproof.definitions.inequality_chains.
Load simplify_chains.
Require Import Reals.
Require Import micromega.Lra.
Open Scope R_scope.

(** Test 0: Go from a chain of inequalities to the statement *)
Goal forall x : R, (& x < 4 <= 5 = 2 + 3 < 10) -> (x < 10).
intro x.
intro H.
Fail ltac1:(lra). (* at this stage, lra does not work yet *)
simpl_ineq_chains ().
ltac1:(lra).
Qed.