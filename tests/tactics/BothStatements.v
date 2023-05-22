Require Import Ltac2.Ltac2.
Require Import Ltac2.Message.

Require Import Waterproof.Waterproof.
Require Import Waterproof.Automation.
Require Import Waterproof.Tactics.
Require Import Waterproof.Util.Assertions.


(** Test 0: This should work *)
Goal forall n : nat, ((n = n) /\ (n + 1 = n + 1)).
Proof.
    intro n.
    We show both statements.
    - We need to show (n = n).
      reflexivity.
    - We need to show (n+1 = n+1).
      reflexivity.
Qed.


(** Test 1: This should also work *)
Goal forall n : nat, ((n = n) /\ (n + 1 = n + 1)).
Proof.
    intro n.
    We prove both statements.
    - We need to show (n = n).
      reflexivity.
    - We need to show (n+1 = n+1).
    reflexivity.
Qed.


(** Test 2: This should raise an error, because the goal is not a  *)
Goal forall n : nat, n <= n.
Proof.
    assert_raises_error (fun() => We show both statements).
Abort.


(** Test 3: This should also work *)
Goal forall n : nat, ((n = n) /\ (n + 1 = n + 1)).
Proof.
    intro n.
    We show both (n = n) and (n + 1 = n + 1).
    reflexivity.
    reflexivity.
Qed.


(** Test 4: This should also work just fine, the order has to be swapped. *)
Goal forall n : nat, ((n = n) /\ (n + 1 = n + 1)).
Proof.
    intro n.
    We show both (n + 1 = n + 1) and (n = n).
    reflexivity.
    reflexivity.
Qed.


(** Test 5: This should print that the second statement is not what is needed to be shown *)
Goal forall n : nat, ((n = n) /\ (n + 1 = n + 1)).
Proof.
    intro n.
    Fail We show both (n = n) and (n + 2 = n + 2).
Abort.


(** Test 6: This should print that the first statement is not what is needed to be shown *)
Goal forall n : nat, ((n = n) /\ (n + 1 = n + 1)).
Proof.
    intro n.
    Fail We show both (n + 2 = n + 2) and (n + 1 = n + 1).
Abort.


(** Test 7: This should print that one of the statements is not what is needed to be shown *)
Goal forall n : nat, ((n = n) /\ (n + 1 = n + 1)).
Proof.
    intro n.
    Fail We show both (n + 2 = n + 2) and (n = n).
Abort.


(** Test 8: This should raise an error: that none of the statemets are what is needed to be shown *)
Goal forall n : nat, ((n = n) /\ (n + 1 = n + 1)).
Proof.
    intro n.
    assert_raises_error (fun () => We show both (n + 2 = n + 2) and (n +3 = n + 3)).
Abort.