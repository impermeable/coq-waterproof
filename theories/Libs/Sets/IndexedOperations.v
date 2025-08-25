Require Import Notations.Common.
Require Import Notations.Sets.

Open Scope subset_scope.

Inductive indexed_intersection {U V : Type} (I : subset V) (X : V -> subset U) : subset U :=
    | index_intersection_intro (x : U) : (forall (i : V), i ∈ I -> x ∈ X i) -> x ∈ (indexed_intersection I X).


Lemma index_intersection_elim {U V : Type} (I : subset V) (X : forall (i : V), subset U) (x : U) :
    x ∈ indexed_intersection I X ⇒ ∀ i ∈ I, x ∈ X i.
Proof.
    intros [y h].
    exact h.
Qed.

Lemma index_intersection_elim_left {U V : Type} (I : subset V) (X : forall (i : V), subset U) (x : U) :
    (∀ i ∈ I, x ∈ X i) ⇒ x ∈ indexed_intersection I X.
Proof.
    intro h.    
    apply index_intersection_intro.
    intros i ih.
    apply h.
    exact ih.
Qed.

Inductive indexed_union {U V : Type} (I : subset V) (X : V -> subset U) : subset U :=
    | index_union_intro (x : U) : (exists (i : V), i ∈ I /\ x ∈ X i) -> x ∈ (indexed_union I X).

Lemma index_union_elim {U V : Type} (I : subset V) (X : forall (i : V), subset U) (x : U) :
    x ∈ indexed_union I X ⇒ ∃ i ∈ I, x ∈ X i.
Proof.
    intros [y h].
    exact h.
Qed.

Lemma index_union_elim_left {U V : Type} (I : subset V) (X : forall (i : V), subset U) (x : U) :
    (∃ i ∈ I, x ∈ X i) ⇒ x ∈ indexed_union I X.
Proof.
    intro h.    
    apply index_union_intro.
    destruct h as [i0 hi0].
    exists i0.
    exact hi0.
Qed.
