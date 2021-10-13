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

(** Test 0: This tests to see if x > 0 or x <= 0 *)
Goal forall x : R, exists n : nat, INR(n) > x.
    intro x.
    Either (x <= 0) or (0 < x).
    - Case (x <= 0).
      Fail Case (x <= 0).
      admit.
    - Fail Case (x <= 0).
      Case (0 < x).
Abort.


(** Test 1: This tests to see if x > 1 or x <= 1 *)
Goal forall x : R, exists n : nat, INR(n) > x.
    intro x.
    Either (x <= 1) or (1 < x).
    - Case (x <= 1).
      Fail Case (x <= 0).
      admit.
    - Fail Case (x <= 0).
      Case (1 < x).
Abort.
Close Scope R_scope.

(** Test 2: Tests the 'Because ... either ... or ...' tactic without specifying types of the 
              alternative hypotheses. *)
Goal forall n : nat, ( ( (n = n) \/ (n + 1 = n + 1) ) -> (n + 1 = n + 1)).
    intro n.
    intro H.
    Because H either n_eq_n or n_plus_1_eq_n_plus_1.
    - Case (n = n).
      admit.
    - Case (n+1 = n+1).
Abort.

(** Test 2: Tests the 'Because ... either ... or ...' tactic with types of the 
              alternative hypotheses. *)
Goal forall n : nat, ( ( (n = n) \/ (n + 1 = n + 1) ) -> (n + 1 = n + 1)).
    intro n.
    intro H.
    Fail Because H either Hn : (n = 0) or HSn : (n+1 = n+1).
    Fail Because H either Hn : (n = n) or HSn : (n+1 = 0).
    Because H either Hn : (n = n) or HSn : (n+1 = n+1).
    - Case (n = n).
      admit.
    - Case (n+1 = n+1).
Abort.
