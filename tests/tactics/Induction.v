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
    - Fail We first show the base case (2 = 2).
      We first show the base case (0 = 0).
      Fail We first show the base case (1 = 1).
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
    - Fail We first show the base case (2 = 2).
      We first show the base case  (0 = 0).
      Fail We first show the base case (1 = 1).
      reflexivity.
    - We now show the induction step.
      Fail We now show the induction step.
      intro IHk.
      reflexivity.
Qed.

(* Test 2: throws error if variable name is 'Qed'
    (quick fix for Waterproof editor / Coq lsp)  *)
Goal forall n : nat, (n = n).
Proof.
    Fail We use induction on Qed.
Abort.

Require Import Waterproof.Notations.Sets.
Open Scope subset_scope.

(* Test 3 : Induction on a variable quantified by
  [∀ x ∈ nat, ...], rather than [∀ x : nat, ...] --
  Case where variable is not introduced yet *)

Goal ∀ n ∈ nat, n >= 0.
Proof.
We use induction on n.
* We first show the base case (0 >= 0).
  We conclude that (0 >= 0).
* We now show the induction step.
  Assume that (n >= 0).
  We need to show that (n + 1 >= 0).
Abort.

(* Test 4: Induction on a variable quantified by
  [∀ x ∈ nat, ...], rather than [∀ x : nat, ...] --
  Case where variable is already introduced  with
  [Take ... ∈ ...] statement *)

Goal ∀ n ∈ nat, n >= 0.
Proof.
Take n ∈ nat.
We use induction on n.
* We first show the base case (0 >= 0).
  We conclude that (0 >= 0).
* We now show the induction step.
  Assume that (n >= 0).
  We need to show that (n + 1 >= 0).
Abort.

(* Test 5: Induction on a variable quantified by
  [∀ x ∈ nat, ...], rather than [∀ x : nat, ...] --
  Case where variable is already introduced,
  with [Take .. : ...] statement *)

Goal ∀ n ∈ nat, n >= 0.
Proof.
Take n : nat.
We use induction on n.
* We first show the base case (0 >= 0).
  We conclude that (0 >= 0).
* We now show the induction step.
  Assume that (n >= 0).
Abort.
