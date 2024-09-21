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

(** By magic it holds that ....  *)

(** Test 0: old notation still works. *)
Goal (0 = 0).
Proof.
  By I it holds that (True) (H1).
Abort.

(** Test 1: postpone proof of claim. Claim added to hypotheses, warning raised. *)
Goal (0 = 0).
Proof.
  assert_feedback_with_string (fun () => By magic it holds that (False) (H2)) Warning
"Please come back later to provide an actual proof of False.".
  assert_feedback_with_string (fun () => By magic it holds that (0 = 1) (H3)) Warning
"Please come back later to provide an actual proof of (0 = 1).".
Abort.

(** By magic we conclude that ...  *)

(** Test 2: old notation still works. *)
Goal (True).
Proof.
  By I we conclude that (True).
Abort.

(** Test 3: postpone proof of conclusion. Raises warning. *)
Goal (0 = 1).
Proof.
  assert_feedback_with_string (fun () => By magic we conclude that (0 = 1)) Warning
"Please come back later to provide an actual proof of (0 = 1).".
Abort.
