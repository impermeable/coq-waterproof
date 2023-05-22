Require Import Ltac2.Ltac2.
Require Import Ltac2.Message.

Require Import Waterproof.Waterproof.
Require Import Waterproof.Automation.
Require Import Waterproof.Tactics.
Require Import Waterproof.Util.Assertions.

(** Test 0: This should work fine *)
Goal forall n : nat, (n = n).
Proof.
    We use induction on n.
    - Fail We first show the base case, namely (2 = 2).
      We first show the base case, namely (0 = 0).
      Fail We first show the base case, namely (1 = 1).
      reflexivity.
    - We now show the induction step.
      Fail We now show the induction step.
      intro IHn.
      reflexivity.
Qed.

(** Test 1: This should work fine *)
Goal (0 = 0) -> forall n : nat, (n = n).
Proof.
    intro n.
    We use induction on k.
    - Fail We first show the base case, namely (2 = 2).
      We first show the base case, namely (0 = 0).
      Fail We first show the base case, namely (1 = 1).
      reflexivity.
    - We now show the induction step.
      Fail We now show the induction step.
      intro IHk.
      reflexivity.
Qed.