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

Require Import Waterproof.Waterproof.
Require Import Waterproof.Tactics.Unfold.
Require Import Waterproof.Util.MessagesToUser.
Require Import Waterproof.Util.Assertions.

Waterproof Enable Redirect Feedback.
Waterproof Enable Redirect Errors.

(* Test 1 : Register a simple notation and use it to expand a definition *)

Local Definition z := 2.

Waterproof Register Unfold "test1" "unfold" "phrase" z.

Goal z = 2.
assert_feedback_with_strings ( fun () =>
    assert_fails_with_string (fun () => Unfold the definition of test1 unfold phrase)
    "Remove this line in the final version of your proof.")
  Info
  ["Expanded definition in statements where applicable.";
  "Hint, replace with: We need to show that (2 = 2)."].
Abort.

(* TODO: add a test for expanding a definition that is defined
in a different module with the framework *)
