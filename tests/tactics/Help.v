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

Waterproof Enable Hypothesis Help.
Waterproof Enable Logging.

(** Test 0 : Suggest to follow advice in goal if goal is wrapped 
  or [False] (i.e. prove contradiction). *)
Goal False.
  Help.
Abort.

(** Test 1 : Only suggest to follow advice in goal if goal is wrapped 
  or [False] (i.e. prove contradiction). *)
Goal (forall n : nat, n = n) -> False.
  intros.
  Help.
Abort.

(** Test 2 : Suggest to solve directly if goal can be shown automatically. *)
Goal True.
  Help.
Abort.

(** Test 3 : Only suggest to solve directly if goal can be shown automatically. *)
Goal (forall n : nat, n = n) -> True.
  intros.
  Help.
Abort.

(** Test 4 : Report \forall hypotheses if available. *)
Goal (forall n : nat, n = n) -> (forall m : nat, m + 1 = m + 1) -> (0 = 1).
  intros.
  Help.
Abort.

(** Test 5 : Report \exists hypotheses if available. *)
Goal (exists n : nat, n = n) -> (exists m : nat, m + 1 = m + 1) -> (0 = 1).
  intros.
  Help.
Abort.

(** Test 6 : Report \forall and \exists hypotheses if available. *)
Goal (forall n : nat, n = n) -> (exists m : nat, m = 0) -> (0 = 1).
  intros.
  Help.
Abort.



(** Test advice how to use newly introduced statements. *)

Require Import Waterproof.Tactics.ItHolds.

(** Test 7: It holds that, no label. *)
Goal False.
Proof.
  It holds that (forall n : nat, n = n).
Abort.

(** Test 8: It holds that, label. *)
Goal False.
Proof.
  It holds that (forall n : nat, n = n) (i).
Abort.

(** Test 9: By ... it holds that, no label. *)
Goal False.
Proof.
  By I it holds that (forall n : nat, True).
Abort.

(** Test 10: Since ... it holds that, no label. *)
Goal False.
Proof.
  Since (True) it holds that (forall n : nat, n = n).
Abort.


Require Import Waterproof.Tactics.Assume.

(** Test 11: Assume that, no label. *)
Goal (forall n : nat, n = n) -> False.
Proof.
  Assume that (forall n : nat, n = n).
Abort.

(** Test 12: Assume that, label. *)
Goal (forall n : nat, n = n) -> False.
Proof.
  Assume that (forall n : nat, n = n) (i).
Abort.

(** Test 13: Assume negation. *)
Goal not (forall n : nat, n = n).
Proof.
  Assume that (forall n : nat, n = n).
Abort.


Require Import Waterproof.Tactics.Claims.

(** Test 14: We claim that, no label. *)
Goal False.
Proof.
  We claim that (forall n : nat, n = n).
Abort.

(** Test 15: Assume that, label. *)
Goal (forall n : nat, n = n) -> False.
Proof.
  We claim that (forall n : nat, n = n) (i).
Abort.

Waterproof Disable Hypothesis Help.

(** Test 16: Test if no advice is indeed given if help is disabled. *)
Goal False.
Proof.
  It holds that (forall n : nat, n = n).
Abort.

Ltac2 Eval (get_feedback_log Info).
