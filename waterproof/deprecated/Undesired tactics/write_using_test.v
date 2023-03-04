(** * Testcases for [write_using.v]
Authors: 
    - Lulof Pirée (1363638)
Creation date: 08 June 2021

Contains tactics [Write goal using ...] and [Write ... using ...].
Used to rewrite and finish the goal/hypothesis with a certain equality,
which is then set as a new goal.
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


Require Import Waterproof.message.

Require Import Waterproof.selected_databases.
Require Import Waterproof.set_intuition.Disabled.
Require Import Waterproof.set_search_depth.To_5.
Require Import Waterproof.load_database.All.
Require Import Waterproof.test_auxiliary.
Require Import Waterproof.load_database.DisableWildcard.
Load write_using.


(* -------------------------------------------------------------------------- *)
(** * Testcases for [Write ... using ... as ...] *)

(** * Test 1
    Base case: valid rewrite statement
    in a hypothesis, with correct expected result.
*)
Lemma test_write_using_as_1: forall x y: nat, 5 * (x + y) = 10 -> 5 * x + 5 * y = 10 .
Proof.
    intros x y.
    intros h.
    Write h using (forall n m p : nat, n * (m + p) = n * m + n * p) as (5 * x + 5 * y = 10).
    assert_hyp_has_type @h constr:(5 * x + 5 *y = 10).
    assumption.
Qed.

(** * Test 2
    Error case: valid rewrite statement
    in a hypothesis, but with wrong expected result.
*)
Lemma test_write_using_as_2: forall x y: nat, 5 * (x + y) = 10 -> 5 * x + 5 * y = 10 .
Proof.
    intros x y.
    intros h.
    let result () := Write h using 
        (forall n m p : nat, n * (m + p) = n * m + n * p) 
        as (5 * y + 5 * x = 10)
    in
    assert_raises_error result.
Abort.


(* -------------------------------------------------------------------------- *)
(** * Testcases for [Write goal in ... as ...] *)

(** * Test 1
    Base case: valid rewrite statement
    in a goal, with correct expected result.
*)
Lemma test_write_goal_as_1: forall x y: nat, 5 * (x + y) = 10 -> 5 * x + 5 * y = 10 .
Proof.
    intros x y.
    intros h.
    Write goal using 
        (forall n m p : nat, n * m + n * p = n * (m + p)) 
        as (5 * (x + y) = 10).
    assert_goal_is constr:(5 * (x + y) = 10).
    assumption.
Qed.

(** * Test 2
    Error case: valid rewrite statement
    in a goal, but wrong expected result.
*)
Lemma test_write_goal_as_2: forall x y: nat, 5 * (x + y) = 10 -> 5 * x + 5 * y = 10 .
Proof.
    intros x y.
    intros h.
    let result () :=
        Write goal using 
        (forall n m p : nat, n * m + n * p = n * (m + p)) 
        as (5 * (x + y) = 11)
    in 
    assert_raises_error result.
Abort.