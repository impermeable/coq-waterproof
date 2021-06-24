(** * rewrite_using_test.v
Authors: 
    - Lulof Pirée (1363638)
Creation date: 08 June 2021

Various versions of [Rewrite using ...] tactic. 
This tactic is used to rewrite the goal or hypotheses.
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
Require Import Waterproof.load_database.All.
Require Import Waterproof.set_search_depth.To_5.
Require Import Waterproof.set_intuition.Disabled.
Load rewrite_using.
Require Import Waterproof.load_database.DisableWildcard.

Open Scope nat_scope.

(* -------------------------------------------------------------------------- *)
(** * Testcases for [Rewrite using ...] 
    Variant without the [in] clause.
*)

(** * Test 1
    Base case: valid rewrite statement.
    Using same proposition as [Nat.mul_add_distr_l].
*)
Lemma test_rewrite_using_1: forall x y: nat, 5 * (x + y) = 5 * x + 5 * y.
Proof.
    intros x y.
    Check Nat.mul_add_distr_l.
    Rewrite using (forall n m p : nat, n * (m + p) = n * m + n * p).
    assert_goal_is constr:(5 * x + 5 * y = 5 * x + 5 * y).
    reflexivity.
Qed.

(** * Test 2
    Base case: valid rewrite statement.
    Using same proposition as [Nat.add_assoc].
*)
Lemma test_rewrite_using_2: forall x y: nat, x + y + (x + y) = x + y + x + y.
Proof.
    intros x y.
    Check Nat.add_assoc.
    Rewrite using (forall n m p : nat, n + (m + p) = n + m + p).
    assert_goal_is constr:(x + y + x + y = x + y + x + y).
    reflexivity.
Qed.

(** * Test 3
    Error case: unapplicable rewrite statement.
*)
Lemma test_rewrite_using_3: forall x y: nat, x + y + (x + y) = x + y + x + y.
Proof.
    intros x y.
    (* No multiplication is involved in the goal... *)
    let result () := (Rewrite using (forall a b:nat, a * (a + b) = a * a + a * b)) in
    assert_raises_error result.
Abort.

(* -------------------------------------------------------------------------- *)
(** * Testcases for [Rewrite <- using ...] 
    Same as [Rewrite using], but other way around 
    (i.e. rewriting to LHS of theorem).
*)

(** * Test 1
    Base case: valid left rewrite statement.
    Using same proposition as [Nat.mul_add_distr_l].
*)
Lemma test_rewrite_using_left_1: forall x y: nat,  5 * x + 5 * y = 5 * (x + y).
Proof.
    intros x y.
    Rewrite <- using (forall n m p : nat, n * (m + p) = n * m + n * p).
    assert_goal_is constr:(5 * (x + y) = 5 * (x + y)).
    reflexivity.
Qed.

(** * Test 2
    Base case: valid left rewrite statement.
    Using same proposition as [Nat.add_assoc].
*)
Lemma test_rewrite_using_left_2: forall x y: nat,  x + y + x + y = x + y + (x + y).
Proof.
    intros x y.
    Rewrite <- using (forall n m p : nat, n + (m + p) = n + m + p).
    assert_goal_is constr:(x + y + (x + y) = x + y + (x + y)).
    reflexivity.
Qed.

(** * Test 3
    Error case: unapplicable left rewrite statement.
*)
Lemma test_rewrite_using_3: forall x y: nat, x + y + (x + y) = x + y + x + y.
Proof.
    intros x y.
    (* No multiplication is involved in the goal... *)
    let result () := (Rewrite using (forall a b:nat, a * (a + b) = a * a + a * b)) in
    assert_raises_error result.
Abort.


(* -------------------------------------------------------------------------- *)
(** * Testcases for [Rewrite using ... in ...] 
    Variant with the [in] clause.
*)

(** * Test 1
    Base case: valid rewrite statement
    in a hypothesis.
    Using same proposition as [Nat.mul_add_distr_l].
*)
Lemma test_rewrite_using_in_1: forall x y: nat, 5 * (x + y) = 10 -> 2 = (x + y).
Proof.
    intros x y.
    intros h.
    Rewrite using (forall n m p : nat, n * (m + p) = n * m + n * p) in h.
    assert_hyp_has_type @h constr:(5 * x + 5 * y = 10).
Abort.

(** * Test 2
    Error case: invalid rewrite statement
    in a hypothesis.
*)

Lemma test_rewrite_using_in_2: forall x y: nat, 5 * (x + y) = 10 -> 2 = (x + y).
Proof.
    intros x y.
    intros h.
    Check and_comm.
    (* This is a theorem about propositions 
        -- clearly does not apply here!*)
    let result () := (Rewrite using (forall A B : Prop, A /\ B <-> B /\ A) in h)
    in assert_raises_error result.
Abort.

(* -------------------------------------------------------------------------- *)
(** * Testcases for [Rewrite using <- ... in ...] 
    Left-rewrite variant with the [in] clause.
*)

(** * Test 1
    Base case: valid left-directional rewrite statement
    in a hypothesis.
    Using same proposition as [Nat.mul_add_distr_l].
*)
Lemma test_rewrite_using_in_left_1: forall x y: nat, 5 * x + 5 * y = 10 -> 5 * (x + y) = 10.
Proof.
    intros x y.
    intros h.
    Rewrite <- using (forall n m p : nat, n * (m + p) = n * m + n * p) in h.
    assert_hyp_has_type @h constr:(5 * (x + y) = 10).
    assumption.
Qed.

(** * Test 2
    Error case: invalid left rewrite statement
    in a hypothesis.
*)
Lemma test_rewrite_using_in_left_2: forall x y: nat, 5 * (x + y) = 10 -> 2 = (x + y).
Proof.
    intros x y.
    intros h.
    (* This is a theorem about propositions 
        -- clearly does not apply here!*)
    let result () := (Rewrite <- using (forall A B : Prop, A /\ B <-> B /\ A) in h)
    in assert_raises_error result.
Abort.