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

(** First test: test all syntax variants **)
Lemma one_is_one: 1 = 1.
Proof.
  We need to show (1 = 1).
  We need to show that (1 = 1).
  We need to show : (1 = 1).
  We need to show that : (1 = 1).
  To show (1 = 1).
  To show that (1 = 1).
  To show that : (1 = 1).
  To show : (1 = 1).
  reflexivity.
Qed.


(** Second test: function definitions are judgementally equal to the function name. 
    So they should be interchangeable. *)
Definition double := fun (x: nat) => 2*x.

Lemma with_function_definition: double 2 = 4.
Proof.
  We need to show (double 2 = 4).
  We need to show (2*2 = 4).
  trivial.
Qed.


(** Third test: this should raise an error, as the wrong goal is supplied. *)
Lemma two_is_two: 2 = 2.
Proof.
  Fail We need to show (0 = 2).
  reflexivity.
Qed.