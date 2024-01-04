(******************************************************************************)
(*                  This file is part of Waterproof-lib.                      *)
(*                                                                            *)
(*   Waterproof-lib is free software: you can redistribute it and/or modify   *)
(*    it under the terms of the GNU General Public License as published by    *)
(*     the Free Software Foundation, either version 3 of the License, or      *)
(*                    (at your option) any later version.                     *)
(*                                                                            *)
(*     Waterproof-lib is distributed in the hope that it will be useful,      *)
(*      but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*       MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the         *)
(*               GNU General Public License for more details.                 *)
(*                                                                            *)
(*     You should have received a copy of the GNU General Public License      *)
(*   along with Waterproof-lib. If not, see <https://www.gnu.org/licenses/>.  *)
(*                                                                            *)
(******************************************************************************)

Require Import Ltac2.Ltac2.
Require Import Ltac2.Message.

Require Import Waterproof.Waterproof.
Require Import Waterproof.Automation.
Require Import Waterproof.Tactics.
Require Import Waterproof.Util.Assertions.

(** Test 0: this should work *)
Goal forall n : nat, ((n = n) <-> (n + 1 = n + 1)).
    intro n.
    We show both directions.
    - We need to show that ( n = n -> n + 1 = n + 1 ).
      admit.
    - We need to show that ( n + 1 = n + 1 -> n = n ).
Abort.


(** Test 1: this should also work *)
Goal forall n : nat, ((n = n) <-> (n + 1 = n + 1)).
    intro n.
    We prove both directions.
    - We need to show that ( n = n -> n + 1 = n + 1 ).
      admit.
    - We need to show that ( n + 1 = n + 1 -> n = n ).
Abort.

(** Test 2: This should raise an error, because the goal is not an if and only if*)
Goal forall n : nat, n <= n.
    Fail We show both directions.
Abort.