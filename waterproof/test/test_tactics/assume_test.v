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

(** * Test 1: single hypothesis, unnamed.
*)
Goal forall n, n = 1 /\ n = 2 -> False.
    intros n.
    Assume that (n = 1 /\ n = 2).
Abort.

(** * Test 2: single hypothesis, named.
*)
Goal forall A B C: Prop, (A /\ B) /\ (B /\ C) -> (A /\ C).
    intros A B C.
    Assume that ((A /\ B) /\ (B /\ C)) (i).
    assert_hyp_has_type @i constr:((A /\ B) /\ (B /\ C)).
Abort.

(** * Test 3: two hypotheses, assume separately, but with a single tactic, both unnamed.
*)
Goal forall A B C: Prop, (A /\ B) -> (B /\ C) -> (A /\ C).
    intros A B C.
    Assume that (A /\ B) and (B /\ C).
Abort.

(** * Test 4: two hypotheses, assume separately, but with a single tactic, second unnamed.
*)
Goal forall A B C: Prop, (A /\ B) -> (B /\ C) -> (A /\ C).
    intros A B C.
    Assume that (A /\ B) (i) and (B /\ C).
    assert_hyp_has_type @i constr:(A /\ B).
Abort.

(** * Test 5: two hypotheses, assume separately, but with a single tactic, first unnamed.
*)
Goal forall A B C: Prop, (A /\ B) -> (B /\ C) -> (A /\ C).
    intros A B C.
    Assume that (A /\ B) and (B /\ C) (i).
    assert_hyp_has_type @i constr:(B /\ C).
Abort.

(** * Test 6: two hypotheses, assume separately using a single tactic, both named.
*)
Goal forall A B C: Prop, (A /\ B) -> (B /\ C) -> (A /\ C).
    intros A B C.
    Assume that (A /\ B) (i) and (B /\ C) (ii).
    assert_hyp_has_type @i  constr:(A /\ B).
    assert_hyp_has_type @ii constr:(B /\ C).
Abort.

(** * Test 7: two hypotheses, assume in steps, first unnamed.
*)
Goal forall A B C: Prop, (A /\ B) -> (B /\ C) -> (A /\ C).
    intros A B C.
    Assume that (A /\ B).
    Assume that (B /\ C) (i).
    assert_hyp_has_type @i constr:(B /\ C).
Abort.

(** * Test 8: assume too many hypotheses.
*)
Goal forall A B C: Prop, (A /\ B) -> (A /\ C).
    intros A B C.
    Fail Assume that (A /\ B) and (B /\ C).
Abort.

(** * Test 9: assume wrong hypothesis.
*)
Goal forall A B C: Prop, (A /\ B) -> (A /\ C).
    intros A B C.
    Fail Assume that (A /\ C).
Abort.

(** * Test 10: assume when there is nothing to assume.)
*)
Goal exists n, n > 0.
  Fail Assume that (0 = 0) (i).
Abort.

(** * Test 11: assume a negated expression.)
*)
Goal forall P : Prop, not (not (not P)) -> not P.
  intro P.
  Assume that (not (not (not P))) (i).
  Assume that P.
Abort.

(** * Test 12: assume the wrong negated expression.)
*)
Goal forall P : Prop, not (not (not P)) -> not P.
  intro P.
  Assume that (not (not (not P))) (i).
  Fail Assume that (not P).
Abort.

(** * Test 13: assume something after negated expression.)
*)
Goal forall P : Prop, not (not (not P)) -> not P.
  intro P.
  Assume that (not (not (not P))).
  Fail Assume that P and (0 = 0).
Abort.

(** * Test 14: assume something and negated expression in one go.)
*)
Goal forall P : Prop, not (not (not P)) -> not P.
  intro P.
  Assume that (not (not (not P))) and P.
Abort.

(** * Test 15: should reject trying to construct a map.
*)
Goal nat -> nat.
  Fail Assume that nat (n).
Abort.

(** * Test 16: should reject trying to construct a map.
*)
Goal (0 = 0) -> nat -> nat.
  Fail Assume that (0 = 0) and nat.
  Assume that (0 = 0).
  Fail Assume that nat.
Abort.
