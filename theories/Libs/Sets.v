Require Import Waterproof.Notations.Common.
Require Import Waterproof.Notations.Sets.

Open Scope subset_scope.

Lemma power_set_characterization {U : Type} (X : subset U) (Y : subset U):
    X ⊂ Y ⇒ X ∈ 𝒫(Y).
Proof.
    intro hXY.
    constructor.
    exact hXY.
Qed.

Lemma empty_set_characterization {U : Type} (X : subset U) (x : U):
    X is empty ⇒ x ∈ X ⇒ False.
Proof.
    intros hempty hx.
    exact (hempty x hx).
Qed.