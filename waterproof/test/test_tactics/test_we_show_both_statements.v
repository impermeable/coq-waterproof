(** * Testcases for [we_show_both_statements.v]
Authors: 
    - Cosmin Manea (1298542)
Creation date: 22 May 2021

Test cases for the [We show/prove both directions] tactic.
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


Load we_show_both_statements.
Require Import Waterproof.test_auxiliary.

(** Test 0: This should work *)
Goal forall n : nat, ((n = n) /\ (n + 1 = n + 1)).
Proof.
    intro n.
    We show both statements.
    reflexivity.
    reflexivity.
Qed.


(** Test 1: This should also work *)
Goal forall n : nat, ((n = n) /\ (n + 1 = n + 1)).
Proof.
    intro n.
    We prove both statements.
    reflexivity.
    reflexivity.
Qed.


(** Test 2: This should raise an error, because the goal is not a  *)
Goal forall n : nat, n <= n.
Proof.
    assert_raises_error (fun() => We show both statements).
Abort.


(** Test 3: This should also work *)
Goal forall n : nat, ((n = n) /\ (n + 1 = n + 1)).
Proof.
    intro n.
    We have to show both (n = n) and (n + 1 = n + 1).
    reflexivity.
    reflexivity.
Qed.


(** Test 4: This should also work just fine *)
Goal forall n : nat, ((n = n) /\ (n + 1 = n + 1)).
Proof.
    intro n.
    We have to show both (n + 1 = n + 1) and (n = n).
    reflexivity.
    reflexivity.
Qed.


(** Test 5: This should print that the second statement is not what is needed to be shown *)
Goal forall n : nat, ((n = n) /\ (n + 1 = n + 1)).
Proof.
    intro n.
    We have to show both (n = n) and (n + 2 = n + 2).
Abort.


(** Test 6: This should print that the first statement is not what is needed to be shown *)
Goal forall n : nat, ((n = n) /\ (n + 1 = n + 1)).
Proof.
    intro n.
    We have to show both (n + 2 = n + 2) and (n + 1 = n + 1).
Abort.


(** Test 7: This should print that one of the statements is not what is needed to be shown *)
Goal forall n : nat, ((n = n) /\ (n + 1 = n + 1)).
Proof.
    intro n.
    We have to show both (n + 2 = n + 2) and (n = n).
Abort.


(** Test 8: This should raise an error: that none of the statemets are what is needed to be shown *)
Goal forall n : nat, ((n = n) /\ (n + 1 = n + 1)).
Proof.
    intro n.
    assert_raises_error (fun () => We have to show both (n + 2 = n + 2) and (n +3 = n + 3)).
Abort.