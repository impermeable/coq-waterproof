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
Require Import Ltac2.Option.

Require Import Waterproof.Waterproof.
Require Import Waterproof.Tactics.Help.
Require Import Waterproof.Util.MessagesToUser.
Require Import Waterproof.Util.Assertions.

Waterproof Enable Hypothesis Help.
Waterproof Enable Redirect Feedback.

(** Test 0 : Suggest to follow advice in goal if goal is wrapped
  or [False] (i.e. prove contradiction). *)
Goal False.
  assert_feedback_with_string (fun () => Help) Info
"Follow the advice in the goal window.".
Abort.

(** Test 1 : Only suggest to follow advice in goal if goal is wrapped
  or [False] (i.e. prove contradiction). *)
Goal (forall n : nat, n = n) -> False.
  intros.
  assert_feedback_with_string (fun () => Help) Info
"Follow the advice in the goal window.".
Abort.

(** Test 2 : Suggest to solve directly if goal can be shown automatically. *)
Goal True.
  assert_feedback_with_string (fun () => Help) Info
"The goal can be shown immediately, use
    We conclude that (...).".
Abort.

(** Test 3 : Only suggest to solve directly if goal can be shown automatically. *)
Goal (forall n : nat, n = n) -> True.
  intros.
  assert_feedback_with_string (fun () => Help) Info
"The goal can be shown immediately, use
    We conclude that (...).".
Abort.

(** Test 4 : Report \forall hypotheses if available. *)
Goal (forall n : nat, n = n) -> (forall m : nat, m + 1 = m + 1) -> (0 = 1).
  intros.
  assert_feedback_with_strings (fun () => Help) Info
["No direct hint available.
Does the goal contain a definition that can be expanded?";
"To use one of the ‘for all’-statements (∀)";
"    (forall n : nat, n = n)";
"    (forall m : nat, m + 1 = m + 1)";
"use";
"    Use ... := (...) in (...)."].
Abort.

(** Test 5 : Report \exists hypotheses if available. *)
Goal (exists n : nat, n = n) -> (exists m : nat, m + 1 = m + 1) -> (0 = 1).
  intros.
  assert_feedback_with_strings (fun () => Help) Info
["No direct hint available.
Does the goal contain a definition that can be expanded?";
"To use one of the ‘there exists’-statements (∃)";
"    (exists n : nat, n = n)";
"    (exists m : nat, m + 1 = m + 1)";
"use";
"    Obtain ... according to (...)."].
Abort.

(** Test 6 : Report \forall and \exists hypotheses if available. *)
Goal (forall n : nat, n = n) -> (exists m : nat, m = 0) -> (0 = 1).
  intros.
  assert_feedback_with_strings (fun () => Help) Info
["No direct hint available.
Does the goal contain a definition that can be expanded?";
"To use one of the ‘for all’-statements (∀)";
"    (forall n : nat, n = n)";
"use";
"    Use ... := (...) in (...).";
"To use one of the ‘there exists’-statements (∃)";
"    (exists m : nat, m = 0)";
"use";
"    Obtain ... according to (...)."].
Abort.



(** Test advice how to use newly introduced statements. *)

Require Import Waterproof.Tactics.ItHolds.

(** Test 7: It holds that, no label. *)
Goal False.
Proof.
  assert_feedback_with_strings
  (fun () => It holds that (forall n : nat, n = n)) Info
["To use (forall n : nat, n = n), use";
"    Use ... := (...) in (...)."].
Abort.

(** Test 8: It holds that, label. *)
Goal False.
Proof.
  assert_feedback_with_strings
  (fun () => It holds that (forall n : nat, n = n) (i)) Info
["To use (forall n : nat, n = n), use";
"    Use ... := (...) in (i)."].
Abort.

(** Test 9: By ... it holds that, no label. *)
Goal False.
Proof.
  (** TODO: is this consistent with the statement
      without the by clause and with the since clause? *)
  By I it holds that (forall n : nat, True).
Abort.

(** Test 10: Since ... it holds that, no label. *)
Goal False.
Proof.
  assert_feedback_with_strings
  (fun () => Since (True) it holds that (forall n : nat, n = n))
  Info
["To use (forall n : nat, n = n), use";
"    Use ... := (...) in (...)."].
Abort.


Require Import Waterproof.Tactics.Assume.

(** Test 11: Assume that, no label. *)
Goal (forall n : nat, n = n) -> False.
Proof.
  assert_feedback_with_strings
  (fun () => Assume that (forall n : nat, n = n))
  Info
["To use (forall n : nat, n = n), use";
"    Use ... := (...) in (...)."].
Abort.

(** Test 12: Assume that, label. *)
Goal (forall n : nat, n = n) -> False.
Proof.
  assert_feedback_with_strings
  (fun () => Assume that (forall n : nat, n = n) (i))
  Info
["To use (forall n : nat, n = n), use";
"    Use ... := (...) in (i)."].
Abort.

(** Test 13: Assume negation. *)
Goal not (forall n : nat, n = n).
Proof.
  assert_feedback_with_strings
  (fun () => Assume that (forall n : nat, n = n))
  Info
["To use (forall n : nat, n = n), use";
"    Use ... := (...) in (...)."].
Abort.


Require Import Waterproof.Tactics.Claims.

(** Test 14: We claim that, no label. *)
Goal False.
Proof.
  assert_feedback_with_strings
  (fun () => We claim that (forall n : nat, n = n))
  Info
["After proving (forall n : nat, n = n), use it with";
"    Use ... := (...) in (...)."].
Abort.

(** Test 15: Assume that, label. *)
Goal (forall n : nat, n = n) -> False.
Proof.
  assert_feedback_with_strings
  (fun () => We claim that (forall n : nat, n = n) (i))
  Info
["After proving (forall n : nat, n = n), use it with";
"    Use ... := (...) in (i)."].
Abort.

Waterproof Disable Hypothesis Help.

(** Test 16: Test if no advice is indeed given if help is disabled. *)
Goal False.
Proof.
  assert_no_feedback
  (fun () => It holds that (forall n : nat, n = n))
  Info.
Abort.
