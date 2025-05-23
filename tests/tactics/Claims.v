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

(** Test 0: This should introduce a new subgoal, that n = n, unnamed after
            it is proven. *)
Goal forall n : nat, exists m : nat, (n = m).
Proof.
    intro n.
    We claim that n = n.
    { reflexivity. }
Abort.

(** Test 1: This should introduce a new subgoal, that n = n, named i after
            it is proven. *)
Goal forall n : nat, exists m : nat, (n = m).
Proof.
    intro n.
    We claim that n = n as (i).
    { reflexivity. }
Abort.

(** Test 2: This should work with a boolean statement *)
Goal forall n : nat, exists m : nat, (n = m).
Proof.
  intro n.
  We claim that (true).
Abort.

(** Test 3: This should work with a boolean statement *)
Goal forall n : nat, exists m : nat, (n = m).
Proof.
  intro n.
  We claim that (orb false true).
Abort.
