Require Import Ltac2.Ltac2.
Require Import Ltac2.Message.

Require Import Waterproof.Waterproof.
Require Import Waterproof.Automation.
Require Import Waterproof.Tactics.
Require Import Waterproof.Util.Assertions.

(** Test 0: this should work *)
Goal forall n : nat, ((n = n) <-> (n + 1 = n + 1)).
    intro n.
    We show both directions.
    - We need to show that ( n = n -> n + 1 = n + 1 ).
      admit.
    - We need to show that ( n + 1 = n + 1 -> n = n ).
Abort.


(** Test 1: this should also work *)
Goal forall n : nat, ((n = n) <-> (n + 1 = n + 1)).
    intro n.
    We prove both directions.
    - We need to show that ( n = n -> n + 1 = n + 1 ).
      admit.
    - We need to show that ( n + 1 = n + 1 -> n = n ).
Abort.

(** Test 2: This should raise an error, because the goal is not an if and only if*)
Goal forall n : nat, n <= n.
    assert_raises_error (fun() => We show both directions).
Abort.