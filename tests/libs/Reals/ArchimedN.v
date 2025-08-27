Require Import Waterproof.Tactics.
Require Import Waterproof.Notations.Common.
Require Import Waterproof.Notations.Sets.
Require Import Waterproof.Notations.Reals.
Require Import Waterproof.Automation.
Require Import Waterproof.Libs.Reals.ArchimedN.

Require Import Stdlib.Reals.Reals.

Waterproof Enable Automation RealsAndIntegers.

Open Scope R_scope.
Open Scope subset_scope.

(* Test 1: Basic archimedN lemma with positive real *)
Lemma test_archimedN_positive : exists n : nat, INR(n) > 5.
Proof.
    exact (archimedN 5).
Qed.

(* Test 2: archimedN lemma with zero *)
Lemma test_archimedN_zero : exists n : nat, INR(n) > 0.
Proof.
    exact (archimedN 0).
Qed.

(* Test 3: archimedN lemma with negative real *)
Lemma test_archimedN_negative : exists n : nat, INR(n) > (-3).
Proof.
    exact (archimedN (-3)).
Qed.

(* Test 4: Basic archimedN_exists lemma with positive real *)
Lemma test_archimedN_exists_positive : ∃ n ∈ ℕ, INR n > 10.
Proof.
    exact (the Archimedean property 10).
Qed.

(* Test 5: archimedN_exists with zero *)
Lemma test_archimedN_exists_zero : ∃ n ∈ ℕ, INR n > 0.
Proof.
    destruct (archimedN 0) as [m hm].
    exists m.
    split.
    { unfold subset_in; unfold conv; trivial. }
    exact hm.
Qed.

(* Test 6: archimedN_exists with negative real *)
Lemma test_archimedN_exists_negative : ∃ n ∈ ℕ, n > (-7).
Proof.
    By the Archimedean property we conclude that (∃ n ∈ ℕ, n > (-7)).
Qed.

(* Test 7: Testing practical application with fraction *)
Lemma test_archimedN_fraction : exists n : nat, INR(n) > (1/2).
Proof.
    exact (archimedN (1/2)).
Qed.

(* Test 8: Using archimedN to prove specific bound *)
Lemma test_specific_bound : ∃ n ∈ ℕ, n > 3.14.
Proof.
    By the Archimedean property we conclude that (∃ n ∈ ℕ, n > 3.14).
Qed.
