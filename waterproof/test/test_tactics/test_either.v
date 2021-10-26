(** * Testcases for [either.v]
Authors: 
    - Cosmin Manea (1298542)
    - Jelle Wemmenhove

Creation date: 08 June 2021

Testcases for the [Either ... or ...] and [Because ... either ... or ...] tactics.
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

Load either.
Require Import Reals.
Local Open Scope R_scope.

(** Test 0: This tests to see if x <= 0 or 0 < x*)
Goal forall x : R, exists n : nat, INR(n) > x.
    intro x.
    Either (x <= 0) or (0 < x).
    - Case (x <= 0).
      Fail Case (x <= 0).
      admit.
    - Fail Case (x <= 0).
      Case (0 < x).
Abort.

(** Test 2: This tests to see if x > 0 or x <= 0 (test commutativity, flipping one term) *)
Goal forall x : R, exists n : nat, INR(n) > x.
    intro x.
    Either  (x > 0) or (x <= 0).
    - Case (x > 0).
      Fail Case (x < 0).
      admit.
    - Fail Case (x > 0).
      Case (x <= 0).
Abort.


(** Test 3: This tests to see if x > 1 or x <= 1 *)
Goal forall x : R, exists n : nat, INR(n) > x.
    intro x.
    Either (x <= 1) or (1 < x).
    - Case (x <= 1).
      Fail Case (x <= 0).
      admit.
    - Fail Case (x <= 0).
      Case (1 < x).
Abort.

(** Test 4: This tests to see what error is thrown if we try a nonsense case analysis. *)
Goal forall x : R, exists n : nat, INR(n) > x.
    intro x.
    Fail Either (x <= 1) or (0 = 0).
Abort.

(** Test 5: This tests whether given x >= 0, either x > 0 or x = 0. 
            Also tests whether the hypothesis name from the tactic can be chosen flexibly. *)
Goal forall x : R, x >= 0 -> exists n : nat, INR(n) > x.
    intros x h.
    Either (x = 0) or (x > 0).
    - Case (x = 0).
      admit.
    - Case (x > 0).
Abort.

(** Test 6: This tests whether given x >= 0, either x = 0 or x > 0 (commutativity). *)
Goal forall x : R, x >= 0 -> exists n : nat, INR(n) > x.
    intros x H.
    Either (x = 0) or (x > 0).
    - Case (x = 0).
      admit.
    - Case (x > 0).
Abort.


(** Test 7: This tests to see if 0 < x, x = 0 or 0 < x. *)
Goal forall x : R, exists n : nat, INR(n) > x.
    intro x.
    Either (x < 0), (x = 0) or (0 < x).
    - Case (x < 0).
      admit.
    - Case (x = 0).
      admit.
    - Case (0 < x).
Abort.

(** Test 8: This tests to see if x = 0, x < 0 or 0 < x (commutativity, flipped sign). *)
Goal forall x : R, exists n : nat, INR(n) > x.
    intro x.
    Either (x = 0), (x < 0) or (0 < x).
    - Case (x = 0).
      admit.
    - Case (x < 0).
      admit.
    - Case (0 < x).
Abort.

(** Test 9: This tests to see if 0 < x, x = 0 or x > 0, (flipped sign). *)
Goal forall x : R, exists n : nat, INR(n) > x.
    intro x.
    Either (x < 0), (x = 0) or (x > 0).
    - Case (x < 0).
      admit.
    - Case (x = 0).
      admit.
    - Case (0 < x). (* Note that this also works although the literal case is x > 0 =) *)
Abort.

Close Scope R_scope.
