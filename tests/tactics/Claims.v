Require Import Ltac2.Ltac2.
Require Import Ltac2.Message.

Require Import Waterproof.Waterproof.
Require Import Waterproof.Automation.
Require Import Waterproof.Tactics.
Require Import Waterproof.Util.Assertions.

(** Test 0: This should introduce a new subgoal, that n = n, unnamed after
            it is proven. *)
Goal forall n : nat, exists m : nat, (n = m).
Proof.
    intro n.
    We claim that (n = n).
    { reflexivity. }
Abort.

(** Test 1: This should introduce a new subgoal, that n = n, named i after
            it is proven. *)
Goal forall n : nat, exists m : nat, (n = m).
Proof.
    intro n.
    We claim that (n = n) (i).
    { reflexivity. }
Abort.