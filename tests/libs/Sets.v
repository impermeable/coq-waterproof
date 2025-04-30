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

(* Test charcterization of empty*)
Goal [0] is empty.
Proof.
    It suffices to show (∀ x ∈ [0], False).
    Take x ∈ [0].
    It holds that (x < 0)%nat.
    Contradiction.
Qed.

#[local] Parameter (X Y W : subset nat).

Waterproof Disable Filter Errors.
Goal X ⊂ Y ⇒ 𝒫(X) ⊂ 𝒫(Y).
Proof.
    Assume that (X ⊂ Y).
    It suffices to show (∀ s ∈ 𝒫(X), s ∈ 𝒫(Y)).
    Take s ∈ (𝒫(X)).
    It suffices to show (s ⊂ Y).
Abort.