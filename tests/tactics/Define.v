Require Import Ltac2.Ltac2.
Require Import Ltac2.Message.

Require Import Coq.Reals.Reals.

Require Import Waterproof.Waterproof.
Require Import Waterproof.Automation.
Require Import Waterproof.Tactics.
Require Import Waterproof.Util.Assertions.

(** Test 0: This should work just fine *)
Goal forall n : nat, ((n = n) /\ (n + 1 = n + 1)).
    intro n.
    Define m := n.
Abort.


(** Test 1: This should also work *)
Goal (0 = 0) -> forall n : nat, ((n = n) \/ (n + 1 = n + 1)).
    intros h n.
    Fail Define h := n.
    Define m := n.
Abort.
