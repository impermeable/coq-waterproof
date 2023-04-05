(** * Testcases for [it_suffices_to_show.v]
Authors: 
    - Lulof Pirée (1363638)
Creation date: 7 June 2021

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

Require Import Waterproof.set_search_depth.To_5.
Load it_suffices_to_show.
Require Import Waterproof.test_auxiliary.

(* -------------------------------------------------------------------------- *)
(** * Testcases for [It suffices to show that ...] 
    Variant without the [by] clause.
*)

Open Scope nat_scope.

(** * Test 1
    Base case: give a statement that indeed suffices.
*)
Lemma test_it_suffices_1: forall x:nat, x>0 /\ x < 2 -> x = S (0).
Proof.
    intros x.
    It suffices to show that (x = 1).
    (* Old goal should have been proven by the above,
        now the assumption used remains to be proven.*)
    assert_goal_is constr:(x=1).
Abort.

(** * Test 2
    Error case: give a statement does not suffice to complete the proof.
*)
Lemma test_it_suffices_2: forall A B : Prop , A /\ A -> B.
Proof.
    intros A B.
    (* Clearly this statement isn't helpful in proving the goal! *)
    let result () := It suffices to show that (1 + 1 = 2) in
    assert_raises_error result.
Abort.

Require Import Waterproof.load.
Module Import db_Integers := databases(Integers).

Local Parameter f : nat -> nat.
Local Parameter f_increasing : forall m n : nat, m <= n -> f m <= f n.

Lemma test_it_suffices_3: f 1 <= f 2.
    By f_increasing it suffices to show that (1 <= 2).
    assert_goal_is constr:(1 <= 2).
Abort.

(** * Test 2
    Error case: give a statement does not suffice to complete the proof.
*)
Lemma test_it_suffices_2: forall A B : Prop , A /\ A -> B.
Proof.
    intros A B.
    (* Clearly this statement isn't helpful in proving the goal! *)
    let result () := By (f_increasing) it suffices to show that (1 + 1 = 2) in
    assert_raises_error result.
Abort.

(* -------------------------------------------------------------------------- *)
(** * Testcases for [It suffices to show that ... by ...] 
    Variant with the [by] clause.
*)

(** * Test 1
    Basic case: correct tactic given, but useless statement.
*)

(*
Lemma test_it_suffices_by_1: 0 <> 1.
Proof.
    It suffices to show that (0 = 0) by (trivial).
Abort.


Inductive even : nat -> Prop :=
    even0 : even 0
  | evenS : forall x:nat, even x -> even (S (S x)).


(** * Test 2
    Basic case: correct tactic given, and usefull statement.
*)
Lemma test_it_suffices_by_2: even 4.
Proof.
    It suffices to show that (even 2) by (apply evenS;assumption).
Abort.

(** * Test 3
    Error case: the given tactic does not prove it.
*)
Lemma test_it_suffices_by_3: 0 <> 1.
Proof.
    let result () := It suffices to show that (1 <> 0) by reflexivity in
    assert_raises_error result.
Abort.
*)
