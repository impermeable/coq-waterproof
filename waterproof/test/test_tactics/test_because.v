(** * Testcases for [because.v]
Authors: 
    - Cosmin Manea (1298542)

Creation date: 30 May 2021

Testcases for the [By ... we know ...] tactic.
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
Load because.

(** Test 0: This should work *)
Goal forall n : nat, ( ( (n = n) /\ (n + 1 = n + 1) ) -> (n + 1 = n + 1)).
    intro n.
    intro H.
    Because H both n_eq_n and n_plus_1_eq_n_plus_1.
Abort.


(** Test 1: This should ~not~ work *)
Goal forall n : nat, ( ( (n = n) /\ (n + 1 = n + 1) ) -> (n + 1 = n + 1)).
    intro n.
    intro H.
    Because H both n_eq_n : nat and n_plus_1_eq_n_plus_1 : nat.
Abort.


