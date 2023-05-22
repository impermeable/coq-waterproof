Require Import Ltac2.Ltac2.
Require Import Ltac2.Message.

Require Import Waterproof.Waterproof.
Require Import Waterproof.Automation.
Require Import Waterproof.Tactics.
Require Import Waterproof.Util.Assertions.

Definition some_function  (x: nat) := 2 * x.
Definition other_function (x: nat) := 2 * x.

(** * Test 3
    Unfold functions IN THE GOAL to show that its definition
    proves the goal.
*)
Lemma test_unfold_3: forall (x:nat), some_function (other_function x) = 2*(2*x).
    intros x.
    Expand the definition of some_function.
    Fail That is, write the goal as (0 = 0).
    That is, write the goal as (2 * other_function x = 2 * (2 * x)).
    Expand the definition of other_function.
    That is, write the goal as (2*(2*x) = 2*(2*x)).
    reflexivity.
Qed.


(** * Test 4
    Unfold functions IN THE GOAL to show that its definition
    proves the goal, using we_need_to_show notation.
*)
Lemma test_unfold_4: forall (x:nat), some_function (other_function x) = 2*(2*x).
    intros x.
    Expand the definition of some_function.
    We need to show (2 * other_function x = 2 * (2 * x)).
    reflexivity.
Qed.


(** * Test 5
    Unfold functions IN A HYPOTHESIS to show that its definition
    proves the goal.
*)
Lemma test_unfold_5: forall (x a:nat), some_function (other_function x) = a -> False.
    intros x a i.
    Fail Expand the definition of some_function, other_function in (ii).
    Expand the definition of some_function, other_function in (i).
    Fail That is, write (ii) as (2*(2*x) = a).
    Fail That is, write (x) as (2*(2*x) = a).
    Fail That is, write (i) as (0 = 0).
    That is, write (i) as (2*(2*x) = a).
Abort.

(** * Test 6
    Unfold functions IN A HYPOTHESIS to show that its definition
    proves the goal.
*)
Lemma test_unfold_6: forall (x a:nat), some_function (other_function x) = a -> False.
    intros x a i.
    Expand the definition of some_function, other_function in (i).
    That is, write (i) as ( 2 * (2 * x) = a ).
Abort.