Require Import Waterproof.Tactics.
Require Import Waterproof.Notations.Common.
Require Import Waterproof.Notations.Sets.
Require Import Waterproof.Notations.Reals.
Require Import Waterproof.Automation.
Require Import Waterproof.Libs.Integers.Even.

Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Zeven.

Waterproof Enable Automation RealsAndIntegers.

Open Scope subset_scope.
Open Scope Z_scope.

(* Test 0: Basic Zeven_char lemma - forward direction *)
Lemma test_Zeven_char : Zeven 6 ⇒ ∃m ∈ ℤ, 6 = 2*m.
Proof.
    Assume that (Zeven 6).
    By Zeven_char it holds that (∃m ∈ ℤ, 6 = 2*m).
    We conclude that (∃m ∈ ℤ, 6 = 2*m).
Qed.

(* Test 1: Basic Zeven_char_inv lemma - reverse direction *)
Lemma test_Zeven_char_inv : (∃m ∈ ℤ, 8 = 2*m) ⇒ Zeven 8.
Proof.
    Assume that (∃m ∈ ℤ, 8 = 2*m).
    By Zeven_char_inv it holds that (Zeven 8).
    We conclude that (Zeven 8).
Qed.

(* Test 2: Concrete even number verification *)
Lemma test_concrete_even : Zeven 10.
Proof.
    By Zeven_char_inv it suffices to show that (∃m ∈ ℤ, 10 = 2*m).
    Choose m := 5.
    { Indeed, m ∈ ℤ. }
    We conclude that (10 = 2*m).
Qed.

(* Test 3: Basic Zodd_char lemma - forward direction *)
Lemma test_Zodd_char : Zodd 7 ⇒ ∃m ∈ ℤ, 7 = 2*m+1.
Proof.
    Assume that (Zodd 7).
    By Zodd_char it holds that (∃m ∈ ℤ, 7 = 2*m+1).
    We conclude that (∃m ∈ ℤ, 7 = 2*m+1).
Qed.

(* Test 4: Basic Zodd_char_inv lemma - reverse direction *)
Lemma test_Zodd_char_inv : (∃m ∈ ℤ, 9 = 2*m+1) ⇒ Zodd 9.
Proof.
    Assume that (∃m ∈ ℤ, 9 = 2*m+1).
    By Zodd_char_inv it holds that (Zodd 9).
    We conclude that (Zodd 9).
Qed.

(* Test 5: Concrete odd number verification *)
Lemma test_concrete_odd : Zodd 11.
Proof.
    By Zodd_char_inv it suffices to show that (∃m ∈ ℤ, 11 = 2*m+1).
    Choose m := 5.
    { Indeed, m ∈ ℤ. }
    We conclude that (11 = 2*m+1).
Qed.

(* Test 6: Testing even_tactic *)
Lemma test_even_tactic : Zeven 14.
Proof.
    apply (even_tactic 7 14).
    reflexivity.
Qed.

(* Test 7: Testing odd_tactic *)
Lemma test_odd_tactic : Zodd 15.
Proof.
    apply (odd_tactic 7 15).
    reflexivity.
Qed.

(* Test 8: Zero is even *)
Lemma test_zero_even : Zeven 0.
Proof.
    By Zeven_char_inv it suffices to show that (∃m ∈ ℤ, 0 = 2*m).
    Choose m := 0.
    { Indeed, m ∈ ℤ. }
    We conclude that (0 = 2*m).
Qed.

(* Test 9: Negative even number *)
Lemma test_negative_even : Zeven (-4).
Proof.
    By Zeven_char_inv it suffices to show that (∃m ∈ ℤ, (-4) = 2*m).
    Choose m := (-2).
    { Indeed, m ∈ ℤ. }
    We conclude that ((-4) = 2*m).
Qed.

(* Test 10: Negative odd number *)
Lemma test_negative_odd : Zodd (-3).
Proof.
    By Zodd_char_inv it suffices to show that (∃m ∈ ℤ, (-3) = 2*m+1).
    Choose m := (-2).
    { Indeed, m ∈ ℤ. }
    We conclude that ((-3) = 2*m+1).
Qed.

(* Test 11: Every integer is either even or odd *)
Lemma test_even_or_odd_specific : Zeven 12 ∨ Zodd 12.
Proof.
    By even_or_odd it holds that (Zeven 12 ∨ Zodd 12).
    We conclude that (Zeven 12 ∨ Zodd 12).
Qed.

(* Test 12: Testing that numbers cannot be both even and odd *)
Lemma test_not_even_and_odd_6 : ¬(Zeven 6 ∧ Zodd 6).
Proof.
    By not_even_and_odd it holds that (¬(Zeven 6 ∧ Zodd 6)).
    We conclude that (¬(Zeven 6 ∧ Zodd 6)).
Qed.

(* Test 13: Verifying specific even characterization - forward direction *)
Lemma test_specific_even_char_forward : Zeven 20 ⇒ ∃m ∈ ℤ, 20 = 2*m.
Proof.
    Assume that (Zeven 20).
    By Zeven_char it holds that (∃m ∈ ℤ, 20 = 2*m).
    We conclude that (∃m ∈ ℤ, 20 = 2*m).
Qed.

(* Test 14: Verifying specific even characterization - backward direction *)
Lemma test_specific_even_char_backward : (∃m ∈ ℤ, 20 = 2*m) ⇒ Zeven 20.
Proof.
    Assume that (∃m ∈ ℤ, 20 = 2*m).
    By Zeven_char_inv it holds that (Zeven 20).
    We conclude that (Zeven 20).
Qed.

(* Test 15: Verifying specific odd characterization - forward direction *)
Lemma test_specific_odd_char_forward : Zodd 21 ⇒ ∃m ∈ ℤ, 21 = 2*m+1.
Proof.
    Assume that (Zodd 21).
    By Zodd_char it holds that (∃m ∈ ℤ, 21 = 2*m+1).
    We conclude that (∃m ∈ ℤ, 21 = 2*m+1).
Qed.

(* Test 16: Verifying specific odd characterization - backward direction *)
Lemma test_specific_odd_char_backward : (∃m ∈ ℤ, 21 = 2*m+1) ⇒ Zodd 21.
Proof.
    Assume that (∃m ∈ ℤ, 21 = 2*m+1).
    By Zodd_char_inv it holds that (Zodd 21).
    We conclude that (Zodd 21).
Qed.

(* Test 17: Large even number test *)
Lemma test_large_even : Zeven 1000.
Proof.
    apply (even_tactic 500 1000).
    reflexivity.
Qed.

(* Test 18: Large odd number test *)
Lemma test_large_odd : Zodd 1001.
Proof.
    apply (odd_tactic 500 1001).
    reflexivity.
Qed.

(* Test 19: Testing even_or_odd with a concrete case *)
Lemma test_concrete_even_or_odd : Zeven 42 ∨ Zodd 42.
Proof.
    By even_or_odd it holds that (Zeven 42 ∨ Zodd 42).
    We conclude that (Zeven 42 ∨ Zodd 42).
Qed.

(* Test 20: Testing that 1 is odd *)
Lemma test_one_is_odd : Zodd 1.
Proof.
    By Zodd_char_inv it suffices to show that (∃m ∈ ℤ, 1 = 2*m+1).
    Choose m := 0.
    { Indeed, m ∈ ℤ. }
    We conclude that (1 = 2*m+1).
Qed.

(* Test 21: Testing that 2 is even *)
Lemma test_two_is_even : Zeven 2.
Proof.
    By Zeven_char_inv it suffices to show that (∃m ∈ ℤ, 2 = 2*m).
    Choose m := 1.
    { Indeed, m ∈ ℤ. }
    We conclude that (2 = 2*m).
Qed.

(* Test 22: Simple conjunction test *)
Lemma test_separate_even_and_odd : Zeven 16.
Proof.
    By Zeven_char_inv it suffices to show that (∃m ∈ ℤ, 16 = 2*m).
    Choose m := 8.
    { Indeed, m ∈ ℤ. }
    We conclude that (16 = 2*m).
Qed.

(* Test 23: Simple odd test for 17 *)
Lemma test_seventeen_is_odd : Zodd 17.
Proof.
    By Zodd_char_inv it suffices to show that (∃n ∈ ℤ, 17 = 2*n+1).
    Choose n := 8.
    { Indeed, n ∈ ℤ. }
    We conclude that (17 = 2*n+1).
Qed.
