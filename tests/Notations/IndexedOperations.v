Require Import Waterproof.Tactics.
Require Import Waterproof.Notations.Common.
Require Import Waterproof.Notations.Sets.
Require Import Waterproof.Notations.IndexedSets.
Require Import Waterproof.Notations.Reals.
Require Import Waterproof.Notations.RealsWithSubsets.
Require Import Waterproof.Automation.
Require Import Waterproof.Chains.
Require Import Waterproof.Libs.Reals.ArchimedN.

Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Require Import Coq.micromega.Lia.


Waterproof Enable Automation RealsAndIntegers.
Waterproof Enable Automation Intuition.
Waterproof Enable Automation Sets.

Open Scope R_scope.
Open Scope subset_scope.
Open Scope R2_scope.

(* Integration test based on Example 2.2.15 of infinite descent *)
(* This tests the indexed intersection notation with real intervals *)
(* This is the main test for indexed operations using real intervals *)

Lemma example_2_2_15_integration_test : (⋂_{n ≥ 1%nat} [0, 1+1/n)) = [0,1].
Proof.
It suffices to show that (⋂_{n ≥ 1%nat} [0, 1+1/n) ⊂ [0,1] ∧ [0,1] ⊂ ⋂_{n ≥ 1%nat} [0, 1+1/n)).
We show both statements.
- We need to show that (⋂_{ n ≥ 1%nat} [0, 1 + 1 / n) ⊂ [0, 1]).
  It suffices to show that (∀ x ∈ ⋂_{ n ≥ 1%nat} [0, 1 + 1 / n), x ∈ [0, 1]).
  Take x ∈ ⋂_{ n ≥ 1%nat} [0, 1 + 1 / n).
  It holds that ∀ n ≥ 1%nat, x ∈ [0, 1 + 1/n) as (i).
  Use n := 1%nat in (i).
  { Indeed, (1 ≥ 1)%nat. }
  It holds that x ∈ [0, 1 + 1 / 1%nat).
  It holds that 1 + 1 / 1%nat = 2.
  It holds that x ∈ [0, 2).
  It holds that x ≥ 0.
  It suffices to show that x ≤ 1.
  We argue by contradiction.
  Assume that ¬ x ≤ 1.
  It holds that x > 1.
  It holds that x - 1 > 0.
  By the Archimedean property it holds that ∃ n ∈ ℕ, n > 1/(x-1).
  Obtain such n.
  It holds that n>1/(x-1).
  It holds that &n > 1/(x-1) > 0.
  It holds that & n*(x-1) > 1/(x-1)*(x-1) = 1.
  It holds that x-1 > 1/n.
  It holds that x > 1 + 1/n.
  Use n:=n in (i).
  { 
    We need to verify that (n ≥ 1)%nat.
    It holds that & n > 1/(x-1) > 0.
    It holds that n ≥ 1.
    We conclude that (n ≥ 1)%nat.
  }
  It holds that x ∈ [0, 1 + 1/n).
  It holds that x < 1 + 1/n.
  It holds that (x > 1 + 1/n) ∧ ¬(x > 1 + 1/n).
  Contradiction.
- We need to show that [0, 1] ⊂ ⋂_{ n ≥ 1%nat} [0, 1 + 1 / n).
  It suffices to show that ∀ x ∈ [0,1], x ∈ ⋂_{n ≥ 1%nat} [0,1 + 1/n).
  Take x ∈ [0,1].
  It suffices to show that ∀ n ≥ 1%nat, x ∈ [0,1 + 1/n).
  Take n ≥ 1%nat.
  It holds that x ≥ 0.
  It holds that n ≥ 1%nat.
  It holds that n ≥ 1.
  It holds that & n ≥ 1 > 0.
  It holds that 1/n > 0.
  It holds that & x ≤ 1 < 1 + 1/n.
  We conclude that x ∈ [0, 1 + 1/n).
Qed.

(* Simple test for indexed union - showing 0 is in the union *)
Lemma test_indexed_union_contains_zero : 
  0 ∈ ⋃_{n ≥ 1%nat} [0, n].
Proof.
It suffices to show that ∃ n ≥ 1%nat, 0 ∈ [0, n].
Choose n := 1%nat.
{ We need to verify that (1 ≥ 1)%nat.
  We conclude that (1 ≥ 1)%nat. }
We need to show that 0 ∈ [0, 1%nat].
It holds that & 0 ≤ 0 ≤ 1.
We conclude that 0 ∈ [0, 1%nat].
Qed.

(* Simple test showing 1/2 is in a union of intervals *)
Lemma test_indexed_union_half : 
  1/2 ∈ ⋃_{n ≥ 1%nat} [0, n].
Proof.
It suffices to show that ∃ n ≥ 1%nat, 1/2 ∈ [0, n].
Choose n := 1%nat.
{ We need to verify that (1 ≥ 1)%nat.
  We conclude that (1 ≥ 1)%nat. }
We need to show that 1/2 ∈ [0, 1%nat].
It holds that & 0 ≤ 1/2 ≤ 1.
We conclude that 1/2 ∈ [0, 1%nat].
Qed.
