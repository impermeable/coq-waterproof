Require Import Waterproof.Tactics.
Require Import Waterproof.Notations.Common.
Require Import Waterproof.Notations.Sets.
Require Import Waterproof.Notations.Reals.
Require Import Waterproof.Automation.
Require Import Waterproof.Libs.Reals.Integer.

Require Import Coq.Reals.Reals.

Waterproof Enable Automation RealsAndIntegers.

Open Scope R_scope.
Open Scope subset_scope.

(* Test 1: Basic Z_in_R membership test *)
Lemma test_Z_in_R_basic : 3 ∈ Z_in_R.
Proof.
    exists 3%Z.
    reflexivity.
Qed.

(* Test 2: Negative integer in Z_in_R *)
Lemma test_Z_in_R_negative : (-5) ∈ Z_in_R.
Proof.
    exists (-5)%Z.
    reflexivity.
Qed.

(* Test 3: Testing plus_Z_in_R lemma *)
Lemma test_plus_Z_in_R : 2 ∈ Z_in_R ⇒ 3 ∈ Z_in_R ⇒ (2 + 3) ∈ Z_in_R.
Proof.
    Assume that (2 ∈ Z_in_R).
    Assume that (3 ∈ Z_in_R).
    By plus_Z_in_R it holds that ((2 + 3) ∈ Z_in_R).
    We conclude that ((2 + 3) ∈ Z_in_R).
Qed.

(* Test 4: Testing minus_Z_in_R lemma *)
Lemma test_minus_Z_in_R : 7 ∈ Z_in_R ⇒ 4 ∈ Z_in_R ⇒ (7 - 4) ∈ Z_in_R.
Proof.
    Assume that (7 ∈ Z_in_R).
    Assume that (4 ∈ Z_in_R).
    By minus_Z_in_R it holds that ((7 - 4) ∈ Z_in_R).
    We conclude that ((7 - 4) ∈ Z_in_R).
Qed.

(* Test 5: Testing mult_Z_in_R lemma *)
Lemma test_mult_Z_in_R : 6 ∈ Z_in_R ⇒ 2 ∈ Z_in_R ⇒ (6 * 2) ∈ Z_in_R.
Proof.
    Assume that (6 ∈ Z_in_R).
    Assume that (2 ∈ Z_in_R).
    By mult_Z_in_R it holds that ((6 * 2) ∈ Z_in_R).
    We conclude that ((6 * 2) ∈ Z_in_R).
Qed.

(* Test 6: Testing zero_Z_in_R lemma *)
Lemma test_zero_Z_in_R : 0 ∈ Z_in_R.
Proof.
    By zero_Z_in_R it holds that (0 ∈ Z_in_R).
    We conclude that (0 ∈ Z_in_R).
Qed.

(* Test 7: Testing one_Z_in_R lemma *)
Lemma test_one_Z_in_R : 1 ∈ Z_in_R.
Proof.
    By one_Z_in_R it holds that (1 ∈ Z_in_R).
    We conclude that (1 ∈ Z_in_R).
Qed.

(* Test 8: Testing two_Z_in_R lemma *)
Lemma test_two_Z_in_R : 2 ∈ Z_in_R.
Proof.
    By two_Z_in_R it holds that (2 ∈ Z_in_R).
    We conclude that (2 ∈ Z_in_R).
Qed.

(* Test 9: Testing INR_1 lemma *)
Lemma test_INR_1 : INR(1%nat) = 1.
Proof.
    By INR_1 it holds that (INR(1%nat) = 1).
    We conclude that (INR(1%nat) = 1).
Qed.

(* Test 10: Testing INR_0 lemma *)
Lemma test_INR_0 : INR(0%nat) = 0.
Proof.
    By INR_0 it holds that (INR(0%nat) = 0).
    We conclude that (INR(0%nat) = 0).
Qed.

(* Test 11: Testing ge_zero_gt_one with concrete example *)
Lemma test_ge_zero_gt_one_concrete : INR 3 > 0 → INR 3 >= 1.
Proof.
    Assume that (INR 3 > 0).
    By ge_zero_gt_one it holds that (INR 3 >= 1).
    We conclude that (INR 3 >= 1).
Qed.

(* Test 12: Demonstrating closure of Z_in_R under operations *)
Lemma test_Z_in_R_closure : (2 + 3) ∈ Z_in_R.
Proof.
    apply plus_Z_in_R.
    { exists 2%Z. reflexivity. }
    { exists 3%Z. reflexivity. }
Qed.
