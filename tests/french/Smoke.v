(******************************************************************************)
(*                  This file is part of Waterproof-lib.                      *)
(******************************************************************************)

(** Smoke test for the French tactic language: exercises a selection of the
    translated tactic keywords end to end. *)

Require Import Ltac2.Ltac2.
Require Import Waterproof.Automation.
Require Import Waterproof.Notations.
Require Import Waterproof.French.

Waterproof Enable Automation RealsAndIntegers.
Waterproof Language French.

Open Scope nat_scope.

(* Take *)
Goal forall n : nat, n = n.
  Soit n : nat.
  Nous concluons que (n = n).
Qed.

(* Assume + conclude *)
Goal (1 = 1) -> (1 = 1).
  Supposons que (1 = 1).
  Nous concluons que (1 = 1).
Qed.

(* Alternative "such that" alias + "It follows" alias *)
Goal (1 = 1) -> (1 = 1).
  On suppose que (1 = 1).
  Il s'ensuit que (1 = 1).
Qed.

(* To show + It suffices to show *)
Goal (0 = 0).
  Nous devons montrer que (0 = 0).
  Il suffit de montrer que (0 = 0).
  Nous concluons que (0 = 0).
Qed.

(* It holds that (introduces a hypothesis) *)
Goal True.
  Il s'avère que (0 = 0).
  Nous concluons que True.
Qed.

(* Both statements *)
Goal (0 = 0) /\ (1 = 1).
  Prouvons les deux énoncés.
  - Nous concluons que (0 = 0).
  - Nous concluons que (1 = 1).
Qed.

(* Contradiction: argue by contradiction *)
Goal (0 = 0).
  Raisonnons par l'absurde.
  Supposons que (0 <> 0).
  Contradiction.
Qed.
