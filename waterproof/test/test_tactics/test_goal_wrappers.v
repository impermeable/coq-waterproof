(** * Testcases for [panic_if_goal_wrapped]

Authors: 
    - Jelle Wemmenhove
Creation date: 08 Oct 2021

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

Require Import Waterproof.test_auxiliary.
Load goal_wrappers.
(* ---------------------------------------------------------------------------*)
(**
    * Testcases for [panic_if_goal_wrapped]
*)

(** * Test 1
    Case Wrapper
*)
Load either.
Load unfold.
Require Import Reals.
Require Waterproof.load.
Import Waterproof.load.databases_RealsAndIntegers.

Local Open Scope R_scope.
Goal R -> False.
    intro x.
    (*assert ({x < 0} + {x >= 0}).
    unfold Rge, Rgt.*)
    Either (x < 0) or (x >= 0).
    Fail Expand the definition of Rlt.
Abort.
Close Scope R_scope.

(** * Test 2
    Induction Wrapper
*)
Load induction.
Load claims.
Goal forall n, n + 0 = n.
    We use induction on n.
    - Fail We claim that nat.
      admit.
    - Fail We claim that (n + 1 + 0 = n + 1) (i).
Abort.

(** * Test 3
    Expand the definition in goal wrapper.
*)
Definition foo (n : nat) := 2 * n.
Definition bar (n : nat) := foo n.
Goal forall n, bar n = n + n.
    intro n.
    Expand the definition of bar.
    Fail Expand the definition of foo.
Abort.


(** * Test 4
    Expand the definition in hypothesis wrapper.
*)
Goal forall n, (bar n = 0) -> (n = 0).
    intros n i.
    Expand the definition of bar in (i).
    Fail Expand the definition of foo in (i).
Abort.

