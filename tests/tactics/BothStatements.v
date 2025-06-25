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


(** Test 0: This should work *)
Goal forall n : nat, ((n = n) /\ (n + 1 = n + 1)).
Proof.
    ltac2: intro n.
    We show both statements.
    - We need to show (n = n).
      ltac2: reflexivity.
    - We need to show (n+1 = n+1).
      ltac2: reflexivity.
Qed.


(** Test 1: This should also work *)
Goal forall n : nat, ((n = n) /\ (n + 1 = n + 1)).
Proof.
    ltac2: intro n.
    We prove both statements.
    - We need to show (n = n).
      ltac2: reflexivity.
    - We need to show (n+1 = n+1).
    ltac2: reflexivity.
Qed.


(** Test 2: This should raise an error, because the goal is not a  *)
Goal forall n : nat, n <= n.
Proof.
    Fail We show both statements.
Abort.


(** Test 3: This should also work *)
Goal forall n : nat, ((n = n) /\ (n + 1 = n + 1)).
Proof.
    ltac2: intro n.
    We show both (n = n) and (n + 1 = n + 1).
    ltac2: reflexivity.
    ltac2: reflexivity.
Qed.


(** Test 4: This should also work just fine, the order has to be swapped. *)
Goal forall n : nat, ((n = n) /\ (n + 1 = n + 1)).
Proof.
    ltac2: intro n.
    We show both (n + 1 = n + 1) and (n = n).
    ltac2: reflexivity.
    ltac2: reflexivity.
Qed.


(** Test 5: This should print that the second statement is not what is needed to be shown *)
Goal forall n : nat, ((n = n) /\ (n + 1 = n + 1)).
Proof.
    ltac2: intro n.
    Fail We show both (n = n) and (n + 2 = n + 2).
Abort.


(** Test 6: This should print that the first statement is not what is needed to be shown *)
Goal forall n : nat, ((n = n) /\ (n + 1 = n + 1)).
Proof.
    ltac2: intro n.
    Fail We show both (n + 2 = n + 2) and (n + 1 = n + 1).
Abort.


(** Test 7: This should print that one of the statements is not what is needed to be shown *)
Goal forall n : nat, ((n = n) /\ (n + 1 = n + 1)).
Proof.
    ltac2: intro n.
    Fail We show both (n + 2 = n + 2) and (n = n).
Abort.


(** Test 8: This should raise an error: that none of the statemets are what is needed to be shown *)
Goal forall n : nat, ((n = n) /\ (n + 1 = n + 1)).
Proof.
    ltac2: intro n.
    Fail We show both (n + 2 = n + 2) and (n +3 = n + 3).
Abort.

Goal forall a b : bool, is_true a -> is_true b -> is_true a /\ is_true b.
    ltac2: intros a b.
    ltac2: intros Ha Hb.
    We show both statements.
    - We need to show that (a).
      ltac2: exact Ha.
    - We conclude that (b).
Qed.
