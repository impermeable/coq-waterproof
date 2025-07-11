Require Import Waterproof.Tactics.
Require Import Waterproof.Notations.Common.
Require Import Waterproof.Notations.Sets.
Require Import Waterproof.Automation.
Waterproof Enable Automation Sets.

Open Scope nat_scope.
Open Scope subset_scope.

(* Test 0: charcterization of empty*)
Goal [0] is empty.
Proof.
    It suffices to show (∀ x ∈ [0], False).
    Take x ∈ [0].
    It holds that (x < 0).
    Contradiction.
Qed.

#[local] Parameter (X Y W : subset nat).

(* Test 1: Characterization of power set (two-ways) *)
Goal X ⊂ Y ⇒ 𝒫(X) ⊂ 𝒫(Y).
Proof.
    Assume that (X ⊂ Y).
    It suffices to show (∀ s ∈ 𝒫(X), s ∈ 𝒫(Y)).
    Take s ∈ (𝒫(X)).
    It suffices to show (s ⊂ Y).
    It holds that (s ⊂ X).
    We need to show (∀ x ∈ s, x ∈ Y).
    Take x ∈ s.
    It holds that (∀ x ∈ s, x ∈ X).
    It holds that (∀ x ∈ X, x ∈ Y).
    We conclude that (x ∈ Y).
Qed.

(* Test 2: Integration test. 
   This could be turned into a performance test by removing the `It holds that`,
   enabling automation for Intuition and RealsAndIntegers, and setting a suitable timeout.
*)
Lemma exercise_2_1_32b (E : subset nat) (p : nat → Prop) : E is empty ⇒ (¬ ∃ x ∈ E, p(x)). 
Proof.
    Assume that (E is empty).
    Assume that (∃ x ∈ E, p(x)). 
    Obtain such x.
    It holds that (x ∈ E).
    Contradiction.
Qed.
