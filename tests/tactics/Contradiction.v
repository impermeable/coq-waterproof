Require Import Ltac2.Ltac2.
Require Import Ltac2.Message.

Require Import Waterproof.Waterproof.
Require Import Waterproof.Automation.
Require Import Waterproof.Notations.
Require Import Waterproof.Tactics.
Require Import Waterproof.Util.Assertions.

(** Test 0: this should start with the proof by contradicition. *)
Goal forall n : nat, n = n.
Proof.
    We argue by contradiction.
    Assume that (¬ (for all n : ℕ, n = n)).
Abort.


(** Test 1: this should work and completely finish the proof. *)
Goal forall n : nat, n = n.
Proof.
    intro n.
    We argue by contradiction.
    Assume that (n ≠ n).
    Contradiction.
Qed.

(** Test 2: this should work and completely finish the proof. *)
Goal forall n : nat, n = n.
Proof.
    intro n.
    We argue by contradiction.
    Assume that (n ≠ n).
    It holds that (n = n). ↯.
Qed.

(** Test 3: wrong assumption specified for wrapper. *)
Goal forall n : nat, n = n.
Proof.
    We argue by contradiction.
    Fail Assume that (¬ (for all n : nat, n ≠ n)).
Abort.