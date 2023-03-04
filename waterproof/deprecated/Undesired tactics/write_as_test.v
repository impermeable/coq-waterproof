(** * Testcases for [write_as.v]
Authors: 
    - Lulof Pirée (1363638)
Creation date: 16 June 2021

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
Require Import Waterproof.load_database.DisableWildcard.


Load write_as.
Require Import Waterproof.test_auxiliary.

Open Scope nat_scope.
Require Import Arith.
Require Import Bool.

(** * Test 1
    Base case: perform a valid rewrite.
*)
Lemma test_write_as_1: forall x, x = 1 + 1 + 1 -> x = 3.
Proof.
    intros x h.
    Write h as (x = 3).
    assert_hyp_has_type @h constr:(x = 3).
    assumption.
Qed.

(** * Test 1
    Error case: invalid rewrite.
*)
Lemma test_write_as_2: forall x, x = 1 + 1 + 1 -> x = 3.
Proof.
    intros x h.
    let result () := Write h as (x = 4) in
    assert_raises_error result.
Abort.