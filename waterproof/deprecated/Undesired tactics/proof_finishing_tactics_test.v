(** * test_proof_finishing_tactics.v
Authors: 
    - Cosmin Manea (1298542)
    - Lulof Pirée (1363638)

Creation date: 06 June 2021

Testcases for the proof finishing tactics.
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
Require Import Waterproof.load_database.All.
Require Import Waterproof.set_search_depth.To_5.
Require Import Waterproof.set_intuition.Disabled.
Require Import Waterproof.tactics.forward_reasoning.proof_finishing_tactics.
Require Import Waterproof.test_auxiliary.
Require Import Waterproof.load_database.DisableWildcard.

(* -------------------------------------------------------------------------- *)
(** * Testcases for [This follows by reflexivity.] 
*)

(** *Test 1:
    Base case: reflexivity applies. *)
Goal forall n : nat, n = n.
    intro n.
    This follows by reflexivity.
Qed.

(** *Test 2:
    Error case: reflecivity does not apply. *)
Goal forall n : nat, (n > 0) -> (n + 1 > n - 1).
    intros n h.
    let result () := This follows by reflexivity in
    assert_raises_error result.
Abort.


(* -------------------------------------------------------------------------- *)
(** * Testcases for [This concludes the proof.] 
*)

(** * Test 1:
    Base case: only one reflexivity step remains,
    so this should indeed finish the proof.  *)
Goal forall n : nat, n = n.
    intro n.
    This concludes the proof.
Qed.

Goal forall A B : Prop, ((A /\ B) -> A).
Proof.
  intros.
  auto 1 with *.
Abort.

(** * Test 2:
    Base case: a transitivity step is enough  *)
Goal forall A B C: Prop, (A -> B) /\ (B -> C) -> (A -> C).
    intros A B C.
    intros h.
    destruct h as [h1 h2].
    intro a.
    This concludes the proof.
Qed.

(** * Test 3:
    Error case: proof is far from finished *)
Goal forall A B C: Prop, (A -> B) -> (A -> C).
    intros A B C.
    intros h.
    let result () := This concludes the proof in
    assert_raises_error result.
Abort.

(* -------------------------------------------------------------------------- *)
(** * Testcases for [This follows by assumption.] 
*)

(** * Test 1:
    Base case: assumption does indeed state goal. *)
Goal forall n : nat, (n = n) -> (n = n).
    intros n h.
    This follows by assumption.
Qed.

(** * Test 2:
    Base case: assumption does indeed state goal. *)
Goal forall A: Prop, A -> A.
    intros A h.
    This follows by assumption.
Qed.

(** * Test 3:
    Error case: no assumption that states the goal. *)
Goal forall A B: Prop, A -> B.
    intros A B h.
    let result () := This follows by assumption in
    assert_raises_error result.
Abort.

(* -------------------------------------------------------------------------- *)
(** * Testcases for [Then ... holds by assumption.] 
*)

(** * Test 1:
    Base case: assumption does indeed state goal. *)
    Goal forall n : nat, (n = n) -> (n = n).
    intros n h.
    Then (n = n) holds by assumption.
Qed.

(** * Test 2:
    Base case: assumption does indeed state goal. *)
Goal forall A: Prop, A -> A.
    intros A h.
    Then (A) holds by assumption.
Qed.

(** * Test 3:
    Error case: no assumption that states the goal. *)
    Goal forall A B: Prop, A -> B.
    intros A B h.
    let result () := Then (B) holds by assumption in
    assert_raises_error result.
Abort.

(** * Test 4:
    Error case: wrong goal given. *)
    Goal forall A: Prop, A -> A.
    intros A h.
    let result () := Then (1 = 1) holds by assumption in
    assert_raises_error result.
Abort.