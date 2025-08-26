Require Import Notations.Common.
Require Import Notations.Sets.

Require Import Sets.Ensembles.

Open Scope subset_scope.

Lemma intersection_characterization {U : Type} (A B : subset U) (x : U):
    x ∈ A ∩ B ⇒ x ∈ A ∧ x ∈ B.
Proof.
    intros [y ha hb].
    split.
    exact ha.
    exact hb.
Qed.

Lemma intersection_characterization_left {U : Type} (A B : subset U) (x : U):
    x ∈ A ∧ x ∈ B ⇒ x ∈ A ∩ B.
Proof.
    intros [ha hb].
    constructor.
    exact ha.
    exact hb.
Qed.

Lemma union_characterization {U : Type} (A B : subset U) (x : U):
    x ∈ A ∪ B ⇒ x ∈ A ∨ x ∈ B.
Proof.
    intros [y ha | y hb].
    {
        left.
        exact ha.
    }
    {
        right.
        exact hb.
    }
Qed.

Lemma union_characterization_left {U : Type} (A B : subset U) (x : U):
    x ∈ A ∨ x ∈ B ⇒ x ∈ A ∪ B.
Proof.
    intros [ha | hb].
    {
        apply Union_introl.
        exact ha.
    }
    {
        apply Union_intror.
        exact hb.
    }
Qed.
