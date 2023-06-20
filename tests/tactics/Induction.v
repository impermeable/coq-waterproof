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

(** Test 0: This should work fine *)
Goal forall n : nat, (n = n).
Proof.
    We use induction on n.
    - Fail We first show the base case, namely (2 = 2).
      We first show the base case, namely (0 = 0).
      Fail We first show the base case, namely (1 = 1).
      reflexivity.
    - We now show the induction step.
      Fail We now show the induction step.
      intro IHn.
      reflexivity.
Qed.

(** Test 1: This should work fine *)
Goal (0 = 0) -> forall n : nat, (n = n).
Proof.
    intro n.
    We use induction on k.
    - Fail We first show the base case, namely (2 = 2).
      We first show the base case, namely (0 = 0).
      Fail We first show the base case, namely (1 = 1).
      reflexivity.
    - We now show the induction step.
      Fail We now show the induction step.
      intro IHk.
      reflexivity.
Qed.