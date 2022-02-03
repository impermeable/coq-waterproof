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
    intro i.
    Because (i) both (n = n) and (n + 1 = n + 1) hold.
Abort.

(** Test 1: This should work, test first prop labeled. *)
Goal forall n : nat, ( ( (n = n) /\ (n + 1 = n + 1) ) -> (n + 1 = n + 1)).
    intro n.
    intro i.
    Because (i) both (n = n) (ii) and (n + 1 = n + 1) hold.
Abort.

(** Test 2: This should work, test second prop labeled. *)
Goal forall n : nat, ( ( (n = n) /\ (n + 1 = n + 1) ) -> (n + 1 = n + 1)).
    intro n.
    intro i.
    Because (i) both (n = n) and (n + 1 = n + 1) (ii) hold.
Abort.

(** Test 3: This should work, test both props labeled. *)
Goal forall n : nat, ( ( (n = n) /\ (n + 1 = n + 1) ) -> (n + 1 = n + 1)).
    intro n.
    intro i.
    Because (i) both (n = n) (ii) and (n + 1 = n + 1) (iii) hold.
Abort.


(** Test 4: This should ~not~ work *)
Goal forall n : nat, ( ( (n = n) /\ (n + 1 = n + 1) ) -> (n + 1 = n + 1)).
    intro n.
    intro i.
    Fail Because (i) both nat and nat hold.
Abort.

(** Test 5: Tests the 'Because ... either ... or ...' tactic without specifying labels of the 
              alternative hypotheses. *)
Goal forall n : nat, ( ( (n = n) \/ (n + 1 = n + 1) ) -> (n + 1 = n + 1)).
    intro n.
    intro i.
    Because (i) either (n = n) or (n + 1 = n + 1) holds.
    - Case (n = n).
      admit.
    - Case (n+1 = n+1).
Abort.

(** Test 6: Tests the 'Because ... either ... or ...' tactic with labels for the 
              alternative hypotheses. *)
Goal forall n : nat, ( ( (n = n) \/ (n + 1 = n + 1) ) -> (n + 1 = n + 1)).
    intro n.
    intro i.
    Fail Because (i) either (n = 0) (ii) or (n+1 = n+1) (iii) holds.
    Fail Because (i) either (n = n) (ii) or (n+1 = 0) (iii) holds.
    Because (i) either (n = n) (ii) or (n+1 = n+1) (iii) holds.
    - Case (n = n).
      admit.
    - Case (n+1 = n+1).
Abort.

(** Test 7 : Tests if the 'Because ... both ... and ...' tactic does not 
             delete the origininal hypothesis *)
Goal forall n : nat, ( ( (n = n) /\ (n + 1 = n + 1) ) -> (n + 1 = n + 1)).
    intro n.
    intro i.
    Fail Because (i) both (n = n) (i) and (n + 1 = n + 1) hold.
    Because (i) both (n = n) and (n + 1 = n + 1) hold.
    Check i.
Abort.

(** Test 8 : Tests if the 'Because ... either ... or ...' tactic does not 
             delete the origininal hypothesis *)
Goal forall n : nat, ( ( (n = n) \/ (n + 1 = n + 1) ) -> (n + 1 = n + 1)).
    intro n.
    intro i.
    Fail Because (i) either (n = n) (i) or (n + 1 = n + 1) holds.
    Because (i) either (n = n) or (n + 1 = n + 1) holds.
    Check i.
Abort.
