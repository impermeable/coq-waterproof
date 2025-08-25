Require Import Waterproof.Tactics.
Require Import Waterproof.Notations.Common.
Require Import Waterproof.Notations.Sets.
Require Import Waterproof.Notations.Reals.
Require Import Waterproof.Automation.
Require Import Waterproof.Libs.Integers.Square.

Require Import Stdlib.ZArith.BinInt.

Waterproof Enable Automation RealsAndIntegers.

Open Scope subset_scope.
Open Scope Z_scope.

(* Test 0: Basic square definition test *)
Lemma test_square_definition : square 3 = 9.
Proof.
    unfold square.
    reflexivity.
Qed.

(* Test 1: Square of zero *)
Lemma test_square_zero : square 0 = 0.
Proof.
    unfold square.
    reflexivity.
Qed.

(* Test 2: Square of negative number *)
Lemma test_square_negative : square (-4) = 16.
Proof.
    unfold square.
    reflexivity.
Qed.

(* Test 3: Basic is_square test *)
Lemma test_is_square_9 : is_square 9.
Proof.
    unfold is_square.
    Choose m := 3.
    { Indeed, m ∈ ℤ. }
    We conclude that (m * m = 9).
Qed.

(* Test 4: is_square with negative root *)
Lemma test_is_square_16_negative : is_square 16.
Proof.
    unfold is_square.
    Choose m := (-4).
    { Indeed, m ∈ ℤ. }
    We conclude that (m * m = 16).
Qed.

(* Test 5: Zero is a perfect square *)
Lemma test_is_square_zero : is_square 0.
Proof.
    unfold is_square.
    Choose m := 0.
    { Indeed, m ∈ ℤ. }
    We conclude that (m * m = 0).
Qed.

(* Test 6: One is a perfect square *)
Lemma test_is_square_one : is_square 1.
Proof.
    unfold is_square.
    Choose m := 1.
    { Indeed, m ∈ ℤ. }
    We conclude that (m * m = 1).
Qed.

(* Test 7: Testing that 25 is a perfect square using direct proof *)
Lemma test_perfect_square_25 : is_square 25.
Proof.
    unfold is_square.
    Choose m := 5.
    { Indeed, m ∈ ℤ. }
    We conclude that (m * m = 25).
Qed.

(* Test 8: Testing that 0 is a perfect square using direct proof *)
Lemma test_perfect_square_zero_direct : is_square 0.
Proof.
    unfold is_square.
    Choose m := 0.
    { Indeed, m ∈ ℤ. }
    We conclude that (m * m = 0).
Qed.

(* Test 9: Testing that 36 is a perfect square with negative root *)
Lemma test_perfect_square_36_negative : is_square 36.
Proof.
    unfold is_square.
    Choose m := (-6).
    { Indeed, m ∈ ℤ. }
    We conclude that (m * m = 36).
Qed.
