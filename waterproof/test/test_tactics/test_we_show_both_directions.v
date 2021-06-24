(** * test_we_show_both_directions.
Authors: 
    - Cosmin Manea (1298542)

Creation date: 22 May 2021

Testcases for the [We show/prove both directions] tactic.
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



Require Import Waterproof.tactics.we_show_both_directions.
Require Import Waterproof.test_auxiliary.

(** Test 0: this should work *)
Goal forall n : nat, ((n = n) <-> (n + 1 = n + 1)).
    intro n.
    We show both directions.
Abort.


(** Test 1: this should also work *)
Goal forall n : nat, ((n = n) <-> (n + 1 = n + 1)).
    intro n.
    We prove both directions.
Abort.


(** Test 2: This should raise an error, because the goal is not an if and only if*)
Goal forall n : nat, n <= n.
    assert_raises_error (fun() => We show both directions).
Abort.