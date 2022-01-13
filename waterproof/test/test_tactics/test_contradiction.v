(** * Testcases for [contradiction.v]
Authors: 
    - Cosmin Manea (1298542)

Creation date: 09 June 2021

Testcases for the [contradiction.v] file.
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


Load contradiction.

Require Import Waterproof.notations.notations.
Require Import Waterproof.AllConstructiveTactics.



(** Test 0: this should start with the proof by contradicition. *)
Goal forall n : nat, n = n.
Proof.
    We argue by contradiction.
    Assume (¬ (for all n : ℕ, n = n)).
Abort.


(** Test 1: this should work and completely finish the proof. *)
Goal forall n : nat, n = n.
Proof.
    intro n.
    We argue by contradiction.
    Assume (n ≠ n).
    Contradiction.
Qed.

(** Test 2: this should work and completely finish the proof. *)
Goal forall n : nat, n = n.
Proof.
    intro n.
    We argue by contradiction.
    Assume (n ≠ n).
    It holds that (n = n). ↯.
Qed.