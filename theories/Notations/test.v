Require Import Waterproof.Tactics.
Require Import Waterproof.Notations.Common.
Require Import Waterproof.Notations.Sets.
Require Import Waterproof.Notations.Reals.
Require Import Waterproof.Chains.
Require Import Waterproof.Automation.
Waterproof Enable Automation Intuition.
Waterproof Enable Automation Sets.
Waterproof Enable Automation RealsAndIntegers.
Require Import Coq.Reals.Reals.

Open Scope R_scope.
Open Scope subset_scope.

Example example_2_1_24 : {x ∈ ℝ | x^2 ≤ 1} = [-1,1].
Proof.
    Unset Printing Notations.
    It suffices to show that ({x ∈ ℝ | x^2 ≤ 1} ⊂ [-1, 1] ∧ [-1, 1] ⊂ {x ∈ ℝ | x^2 ≤ 1}).
Abort.