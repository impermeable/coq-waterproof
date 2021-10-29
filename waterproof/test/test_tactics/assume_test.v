(** * Testcases for [assume.v].
Authors: 
    - Lulof Pirée (1363638)
    - Jelle Wemmenhove
Creation date: 20 May 2021

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
Load assume.

(** * Test 1: single hypothesis.
*)
Goal forall n, n = 1 /\ n = 2 -> False.
    intros n.
    Assume n_is_one_and_n_is_two : (n = 1 /\ n = 2).
    assert_hyp_has_type @n_is_one_and_n_is_two constr:(n = 1 /\ n = 2).
Abort.

(** * Test 2: single hypothesis.
*)
Goal forall A B C: Prop, (A /\ B) /\ (B /\ C) -> (A /\ C).
    intros A B C.
    Assume ab_bc : ((A /\ B) /\ (B /\ C)).
    assert_hyp_has_type @ab_bc constr:((A /\ B) /\ (B /\ C)).
Abort.

(** * Test 3: two hypotheses, assume in one go.
*)
Goal forall A B C: Prop, (A /\ B) -> (B /\ C) -> (A /\ C).
    intros A B C.
    Assume ab : (A /\ B) and bc : (B /\ C).
    assert_hyp_has_type @ab constr:(A /\ B).
    assert_hyp_has_type @bc constr:(B /\ C).
Abort. 

(** * Test 4: two hypotheses, assume in steps.
*)
Goal forall A B C: Prop, (A /\ B) -> (B /\ C) -> (A /\ C).
    intros A B C.
    Assume ab : (A /\ B).
    Assume bc : (B /\ C).
    assert_hyp_has_type @ab constr:(A /\ B).
    assert_hyp_has_type @bc constr:(B /\ C).
Abort.

(** * Test 5: assume too many hypotheses.
*)
Goal forall A B C: Prop, (A /\ B) -> (A /\ C).
    intros A B C.
    Fail Assume ab : (A /\ B) and bc : (B /\ C).
Abort.

(** * Test 6: assume wrong hypothesis.
*)
Goal forall A B C: Prop, (A /\ B) -> (A /\ C).
    intros A B C.
    Fail Assume ac : (A /\ C).
Abort.

(** * Test 7: assume when there is nothing to assume.)
*)
Goal exists n, n > 0.
  Fail Assume h : (0 = 0).
Abort.

(** * Test 8: assume a negated expression.)
*)
Goal forall P : Prop, not (not (not P)) -> not P.
  intro P.
  Assume nnnP : (not (not (not P))).
  Assume H : P.
Abort.

(** * Test 9: assume the wrong negated expression.)
*)
Goal forall P : Prop, not (not (not P)) -> not P.
  intro P.
  Assume nnnP : (not (not (not P))).
  Fail Assume H : (not P).
Abort.

(** * Test 10: assume something after negated expression.)
*)
Goal forall P : Prop, not (not (not P)) -> not P.
  intro P.
  Assume nnnP : (not (not (not P))).
  Fail Assume H : P and h : (0 = 0).
Abort.

(** * Test 10: assume something and negated expression in one go.)
*)
Goal forall P : Prop, not (not (not P)) -> not P.
  intro P.
  Assume nnnP : (not (not (not P))) and H : P.
Abort.

(** * Test 11: should reject trying to construct a map.
*)
Goal nat -> nat.
  Fail Assume n : nat.
Abort.

(** * Test 12: should reject trying to construct a map.
*)
Goal (0 = 0) -> nat -> nat.
  Fail Assume p : (0 = 0) and n : nat.
  Assume p : (0 = 0).
  Fail Assume n : nat.
Abort.
