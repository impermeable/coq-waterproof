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
Require Import Waterproof.Util.MessagesToUser.
Require Import Waterproof.Util.Assertions.

Waterproof Enable Redirect Feedback.

(** Test 0: This should choose m equal to n *)
Goal forall n : nat, exists m : nat, n = m.
Proof.
  intros.
  Choose m := n.
  reflexivity.
Qed.

(** Test 1: This should choose m equal n implicitly *)
Goal forall n : nat, exists m : nat, n = m.
    intro n.
    Choose (n).
    reflexivity.
Qed.


(** Test 2: This should choose m equal to 1 *)
Goal exists m : nat, m = 1.
    Choose m := 1.
    reflexivity.
Qed.


(** Test 3: This should raise an error, as the goal is not an exists goal *)
Goal forall n : nat, ( ( (n = n) \/ (n + 1 = n + 1) ) -> (n + 1 = n + 1)).
    intro n.
    Fail Choose (n).
Abort.


(** Test 4: This should also raise an error, as the goal is not an exists goal *)
Goal forall n : nat, ( ( (n = n) \/ (n + 1 = n + 1) ) -> (n + 1 = n + 1)).
    intro n.
    Fail Choose m := n.
Abort.

(** Test 5: Choose a blank *)
Goal exists n : nat, n + 1 = n + 1.
    assert_feedback_with_string (fun () => Choose n := (_)) Warning
(String.concat "" ["Please come back later to make a definitive choice for n.
For now you can use that "; "
(n = ?n)."]).
Abort.

(** Test 6: Choose a named evar *)
Goal exists n : nat, n + 1 = n + 1.
    assert_feedback_with_string (fun () => Choose n := (?[m])) Warning
(String.concat "" ["Please come back later to make a definitive choice for n.
For now you can use that "; "
(n = ?m)."]).
Abort.

(** Test 7: Choose a blank check that blank was renamed *)
Goal exists n : nat, n + 1 = n + 1.
    assert_feedback_with_string (fun () => Choose n := (_)) Warning
(String.concat "" ["Please come back later to make a definitive choice for n.
For now you can use that "; "
(n = ?n)."]).
    assert (?n = 0).
Abort.

(** Test 8: Choose a more complicated blank and check that renaming took place,
    by reformulating the goal in terms of the new named evars. *)
Goal exists n : nat, n + 1 = n + 1.
    assert_feedback_with_string (fun () => Choose n := (_ + _ + _)) Warning
(String.concat "" ["Please come back later to make a definitive choice for n.
For now you can use that "; "
(n = ?n + ?n0 + ?n1)."]).
    change (?n + ?n0 + ?n1 + 1 = ?n + ?n0 + ?n1 + 1).
Abort.

(** Test 9: Choose a blank without specifying the name of the variable *)
Goal exists n : nat, n + 1 = n + 1.
  assert_feedback_with_string (fun () => Choose (_)) Warning
"Please come back later to make a definite choice.".
  change (?n + 1 = ?n + 1).
Abort.

(** Test 10: Choose a blank if binder has no name *)
Goal exists _ : nat, True.
Proof.
  assert_feedback_with_string (fun () => Choose (_)) Warning
"Please come back later to make a definite choice.".
  (* In this case, the blank evar should be renamed to `x` *)
  assert (?x = 0). (* This checks if ?x exists and can be referred to. *)
Abort.

(** ** Tests about choosing different variable names *)

(** Test 11: Warn on different variable name *)
Goal exists n : nat, n + 1 = n + 1.
Proof.
    assert_feedback_with_strings (fun () => Choose m := 1) Warning
["Expected variable name n instead of m."].
Abort.

(** Test 12: Do not warn on different variable name when binder is shielded,
    because of an already existing definition. *)
Goal exists n : nat, n + 1 = n + 1.
Proof.
    set (n := 3).
    assert_no_feedback (fun () => Choose n0 := 2) Warning.
Abort.
