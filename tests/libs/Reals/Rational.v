Require Import Waterproof.Notations.Common.
Require Import Waterproof.Notations.Sets.
Require Import Waterproof.Notations.Reals.
Require Import Waterproof.Libs.Reals.Rational.
Require Import Waterproof.Libs.Reals.Integer.

Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.

Open Scope R_scope.
Open Scope subset_scope.

(* Test 1: Verify that 1/2 is rational using definition *)
Lemma test_half_is_rational : is_rational (1/2).
Proof.
    unfold is_rational.
    exists 1.
    split.
    - apply one_Z_in_R.
    - exists 2.
      split.
      + apply two_Z_in_R.
      + split.
        * lra.
        * field.
Qed.

(* Test 2: Verify that any integer is rational *)
Lemma test_integer_is_rational : is_rational 5.
Proof.
    apply int_is_rational.
    exists 5%Z.
    reflexivity.
Qed.

(* Test 3: Verify that zero is rational *)
Lemma test_zero_is_rational : is_rational 0.
Proof.
    apply int_is_rational.
    apply zero_Z_in_R.
Qed.

(* Test 4: Test that 1 is rational using integer proof *)
Lemma test_one_is_rational : is_rational 1.
Proof.
    apply int_is_rational.
    apply one_Z_in_R.
Qed.

(* Test 5: Test that 2 is rational using integer proof *)
Lemma test_two_is_rational : is_rational 2.
Proof.
    apply int_is_rational.
    apply two_Z_in_R.
Qed.

(* Test 6: Test plus_frac lemma for fraction addition *)
Lemma test_plus_frac : 1/2 + 1/3 = (1*3 + 1*2)/(2*3).
Proof.
    apply plus_frac.
    - lra.
    - lra.
Qed.

(* Test 7: Test min_frac lemma for fraction subtraction *)
Lemma test_min_frac : 3/4 - 1/2 = (3*2 - 1*4)/(4*2).
Proof.
    apply min_frac.
    - lra.
    - lra.
Qed.

(* Test 8: Test simple rational number *)
Lemma test_simple_fraction : is_rational (1/3).
Proof.
    unfold is_rational.
    exists 1.
    split.
    - apply one_Z_in_R.
    - exists 3.
      split.
      + exists 3%Z.
        reflexivity.
      + split.
        * lra.
        * field.
Qed.

(* Test 9: Test negative fraction is rational *)
Lemma test_negative_fraction_rational : is_rational (-1/4).
Proof.
    unfold is_rational.
    exists (-1).
    split.
    - exists (-1)%Z.
      reflexivity.
    - exists 4.
      split.
      + exists 4%Z.
        reflexivity.
      + split.
        * lra.
        * field.
Qed.

(* Test 10: Test large fraction is rational *)
Lemma test_large_fraction : is_rational (7/11).
Proof.
    unfold is_rational.
    exists 7.
    split.
    - exists 7%Z.
      reflexivity.
    - exists 11.
      split.
      + exists 11%Z.
        reflexivity.
      + split.
        * lra.
        * field.
Qed.

(* Test 11: Test that addition works with simple cases *)
Lemma test_simple_addition : is_rational (1 + 1/2).
Proof.
    apply sum_is_rational.
    - apply int_is_rational.
      apply one_Z_in_R.
    - unfold is_rational.
      exists 1.
      split.
      + apply one_Z_in_R.
      + exists 2.
        split.
        * apply two_Z_in_R.
        * split.
          -- lra.
          -- field.
Qed.

(* Test 12: Test subtraction with simple cases *)
Lemma test_simple_subtraction : is_rational (2 - 1/2).
Proof.
    apply diff_is_rational.
    - apply int_is_rational.
      apply two_Z_in_R.
    - unfold is_rational.
      exists 1.
      split.
      + apply one_Z_in_R.
      + exists 2.
        split.
        * apply two_Z_in_R.
        * split.
          -- lra.
          -- field.
Qed.

(* Test 13: Test basic multiplication *)
Lemma test_basic_multiplication : is_rational (2 * (1/3)).
Proof.
    apply mult_is_rational.
    - apply int_is_rational.
      apply two_Z_in_R.
    - unfold is_rational.
      exists 1.
      split.
      + apply one_Z_in_R.
      + exists 3.
        split.
        * exists 3%Z.
          reflexivity.
        * split.
          -- lra.
          -- field.
Qed.

(* Test 14: Test simple division *)
Lemma test_simple_division : is_rational ((1/2) / 2).
Proof.
    apply div_is_rational.
    - unfold is_rational.
      exists 1.
      split.
      + apply one_Z_in_R.
      + exists 2.
        split.
        * apply two_Z_in_R.
        * split.
          -- lra.
          -- field.
    - apply int_is_rational.
      apply two_Z_in_R.
    - lra.
Qed.

(* Test 15: Test fraction with larger numbers *)
Lemma test_larger_fraction : is_rational (13/17).
Proof.
    unfold is_rational.
    exists 13.
    split.
    - exists 13%Z.
      reflexivity.
    - exists 17.
      split.
      + exists 17%Z.
        reflexivity.
      + split.
        * lra.
        * field.
Qed.
