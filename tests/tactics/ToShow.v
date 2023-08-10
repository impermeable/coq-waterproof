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
  assert_raises_error (fun () => We need to show (0 = 2)).
  reflexivity.
Qed.


(** Test changing goal into equivalent statement.*)
Variable A B C : Prop.
Variable f : A -> B.
Variable g : B -> C.
Variable h : C -> A.

(* Test 4: able to replace equivalent goal. *)
Goal B.
Proof.
  pose f; pose g; pose h.
  We need to show that A.
Abort.

(* Test 5a: unable to replace equivalent goal
  without full proof of equivalence. *)
Goal B.
Proof.
  pose f; pose g.
  Fail We need to show that A.
Abort.
(* Test 5b: missing in other implication *)
Goal A.
Proof.
  pose f; pose g.
  Fail We need to show that B.
Abort.

(* Test 6a: able to replace equivalent goal
  with missing proof step added as extra lemma. *)
Goal B.
Proof.
  pose f; pose g.
  By h we need to show that A.
Abort.
(* Test 6b: missing in other implication. *)
Goal A.
Proof.
  pose f; pose g.
  By h we need to show that B.
Abort.

Variable D : Prop.
Variable k : D.
(* Test 7: fails if superfluous lemma added *)
Goal B.
Proof.
  pose f; pose g; pose h.
  Fail By k we need to show that A.
Abort.

(* Test 8a: fails if no proof equivalence with 
  superfluous lemma added. *)
Goal B.
Proof.
  pose f; pose g.
  Fail By k we need to show that A.
Abort.
(* Test 8b: missing in other implication. *)
Goal A.
Proof.
  pose f; pose g.
  Fail By k we need to show that B.
Abort.
