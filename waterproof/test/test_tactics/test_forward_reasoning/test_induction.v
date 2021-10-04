(** * Testcases for [induction.v]
Authors: 
    - Cosmin Manea (1298542)

Creation date: 06 June 2021

Testcases for the [We prove by induction] tactic.
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

Load induction.


(** Test 0: This should work fine *)
Goal forall n : nat, (n = n) -> (S n = S n).
Proof.
    intro n.
    intro h.
    We use induction on n.
    - Fail We first show the base case, namely (2 = 2).
      We first show the base case, namely (1 = 1).
      Fail We first show the base case, namely (1 = 1).
      reflexivity.
    - We now show the induction step.
      Fail We now show the induction step.
      reflexivity.
Qed.