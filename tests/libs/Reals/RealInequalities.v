Require Import Waterproof.Notations.Common.
Require Import Waterproof.Notations.Sets.
Require Import Waterproof.Notations.Reals.
Require Import Waterproof.Libs.Reals.RealInequalities.

Require Import Stdlib.Reals.Reals.
Require Import Stdlib.micromega.Lra.

Open Scope R_scope.

(* Test 1: Basic test for mult_neq_zero with positive numbers *)
Lemma test_mult_neq_zero_positive : 0 ≠ 2 * 3.
Proof.
    apply mult_neq_zero.
    - lra.
    - lra.
Qed.

(* Test 2: Test mult_neq_zero with negative numbers *)
Lemma test_mult_neq_zero_negative : 0 ≠ (-2) * 3.
Proof.
    apply mult_neq_zero.
    - lra.
    - lra.
Qed.

(* Test 3: Test mult_neq_zero with fractions *)
Lemma test_mult_neq_zero_fractions : 0 ≠ (1/2) * (1/3).
Proof.
    apply mult_neq_zero.
    - lra.
    - lra.
Qed.

(* Test 4: Test mult_neq_zero with mixed positive and negative *)
Lemma test_mult_neq_zero_mixed : 0 ≠ (-5) * (-7).
Proof.
    apply mult_neq_zero.
    - lra.
    - lra.
Qed.

(* Test 5: Basic test for Rdivid_ineq_interchange *)
Lemma test_Rdivid_ineq_interchange_basic : 2 = 6/3 → 3 = 6/2.
Proof.
    intro h.
    apply (Rdivid_ineq_interchange 2 6 3).
    - exact h.
    - lra.
    - lra.
Qed.

(* Test 6: Test Rdivid_ineq_interchange with fractions *)
Lemma test_Rdivid_ineq_interchange_fractions : 1/2 = 3/6 → 6 = 3/(1/2).
Proof.
    intro h.
    apply (Rdivid_ineq_interchange (1/2) 3 6).
    - exact h.
    - lra.
    - lra.
Qed.

(* Test 7: Test Rdivid_ineq_interchange with negative numbers *)
Lemma test_Rdivid_ineq_interchange_negative : (-2) = 8/(-4) → (-4) = 8/(-2).
Proof.
    intro h.
    apply (Rdivid_ineq_interchange (-2) 8 (-4)).
    - exact h.
    - lra.
    - lra.
Qed.

(* Test 8: Test mult_neq_zero with variables close to specific values *)
Lemma test_mult_neq_zero_near_one : 0 ≠ 1.1 * 0.9.
Proof.
    apply mult_neq_zero.
    - lra.
    - lra.
Qed.

(* Test 9: Test that the product of reciprocals is nonzero *)
Lemma test_mult_neq_zero_reciprocals : 0 ≠ (1/4) * (1/5).
Proof.
    apply mult_neq_zero.
    - lra.
    - lra.
Qed.

(* Test 10: Simple test showing product of non-zero terms is non-zero *)
Lemma test_combined_simple : 0 ≠ 3 * (1/4).
Proof.
    apply mult_neq_zero.
    - lra.
    - lra.
Qed.
