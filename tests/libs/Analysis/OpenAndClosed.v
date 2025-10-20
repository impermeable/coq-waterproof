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

Require Import Waterproof.Libs.Analysis.OpenAndClosed.
Require Import Waterproof.Notations.Common.
Require Import Waterproof.Notations.Reals.
Require Import Waterproof.Notations.Sets.
Require Import Waterproof.Util.Assertions.
Require Import Waterproof.Util.MessagesToUser.
Require Import Waterproof.Tactics.

Waterproof Enable Redirect Feedback.
Waterproof Enable Redirect Errors.

Open Scope R_scope.
Open Scope subset_scope.

(* Test 1: Expand the definition of open in goal, and throws an error suggesting
   to remove the line after use. *)
Goal ∀ A : subset ℝ, A is open → A is open.
Proof.
  Take A : (subset ℝ).
  Assume that (A is open).
  assert_feedback_with_strings
  (fun () =>
  assert_fails_with_string
  (fun () => Unfold the definition of open)
"Remove this line in the final version of your proof.")
  Info
["Definition open";
"Hint, insert: We need to show that (∀ a ∈ A, a is an _interior point_ of A).";
"Hint, insert: It holds that (∀ a ∈ A, a is an _interior point_ of A)."].
Abort.

(* Test 2: Fails to expand definition when "open" doesn't appear in statements. *)
Goal ∀ x : ℝ, x = x.
Proof.
  Take x : ℝ.
  assert_feedback_with_strings
  (fun () =>
  assert_fails_with_string
  (fun () => Unfold the definition of open)
"Remove this line in the final version of your proof.")
  Info
["'Definition open' does not appear in any statement."].
Abort.
