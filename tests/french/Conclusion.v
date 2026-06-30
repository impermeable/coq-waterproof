(******************************************************************************)
(*                  This file is part of Waterproof-lib.                      *)
(******************************************************************************)

(** Demonstrates the French language entry point for the Waterproof tactic
    language: French tactic keywords, mutual exclusivity with the English
    keywords, and French user-facing messages. *)

Require Import Ltac2.Ltac2.
Require Import Ltac2.Message.

Require Import Waterproof.Automation.
Require Import Waterproof.French.
Require Import Waterproof.Util.Assertions.

Waterproof Enable Automation RealsAndIntegers.
Waterproof Enable Redirect Errors.
Waterproof Language French.

(* --- French keywords prove goals --- *)
Goal True.
  Nous concluons que True.
Qed.

Goal (0 = 0).
  Il s'ensuit que (0 = 0).
Qed.

Goal True.
  En effet, True.
Qed.

(* "Par magie" postpones the goal (it is admitted) and warns in French. *)
Goal (0 = 0).
  Par magie nous concluons que (0 = 0).
Admitted.

(* --- English keyword is NOT in scope under the French entry (mutually
       exclusive): the line below is a *parse* error if uncommented, because
       "We conclude that ..." is not imported by Waterproof.French. Parse errors
       cannot be caught by [Fail], so it is left here as documentation. ---

   Goal True. We conclude that True. Abort.
*)

(* --- The user-facing error message is in French --- *)
Goal (0 = 1).
  let result () := Nous concluons que (0 = 1) in
  assert_fails_with_string result "Impossible de vérifier que (0 = 1).".
Abort.
