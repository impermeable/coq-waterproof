(** * Testcases for [apply.v]
Authors: 
    - Cosmin Manea (1298542)

Creation date: 06 June 2021

Testcases for the [Apply] tactic.
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

Require Import Waterproof.tactics.apply.

(** Test 0: This should work just fine, by applying a hypothesis *)
Goal forall n : nat, exists m : nat, (n = m).
Proof.
    intro.
    assert (n = n) as X.
    {
        reflexivity.
    }
    pose (m := n).
    exists m.
    Apply X.
Qed.


(** Test 1: This should also work just fine, by applying a lemma *)

Lemma my_refl (n : nat) : n = n.
Proof.
    reflexivity.
Qed.

Goal forall n : nat, n = n.
Proof.
    intro n.
    Apply (my_refl n).
Qed.

