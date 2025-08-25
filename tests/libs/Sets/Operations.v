Require Import Waterproof.Notations.Common.
Require Import Waterproof.Notations.Sets.
Require Import Waterproof.Libs.Sets.Operations.

Require Import Coq.Arith.Arith.
Require Import Coq.micromega.Lia.

Open Scope subset_scope.

(* Helper definitions for testing *)
Definition even_nats : subset nat := fun n => exists k, n = 2 * k.
Definition odd_nats : subset nat := fun n => exists k, n = 2 * k + 1.
Definition small_nats : subset nat := fun n => n < 5.
Definition large_nats : subset nat := fun n => n >= 5.

(* Test 1: Basic intersection characterization *)
Lemma test_intersection_characterization_basic :
    2 ∈ even_nats ∩ small_nats ⇒ 2 ∈ even_nats ∧ 2 ∈ small_nats.
Proof.
    intro h.
    apply intersection_characterization.
    exact h.
Qed.

(* Test 2: Intersection characterization left direction *)
Lemma test_intersection_characterization_left_basic :
    4 ∈ even_nats ∧ 4 ∈ small_nats ⇒ 4 ∈ even_nats ∩ small_nats.
Proof.
    intro h.
    apply intersection_characterization_left.
    exact h.
Qed.

(* Test 3: Union characterization basic *)
Lemma test_union_characterization_basic :
    3 ∈ odd_nats ∪ even_nats ⇒ 3 ∈ odd_nats ∨ 3 ∈ even_nats.
Proof.
    intro h.
    apply union_characterization.
    exact h.
Qed.

(* Test 4: Union characterization left direction *)
Lemma test_union_characterization_left_basic :
    6 ∈ even_nats ∨ 6 ∈ odd_nats ⇒ 6 ∈ even_nats ∪ odd_nats.
Proof.
    intro h.
    apply union_characterization_left.
    exact h.
Qed.

(* Test 5: Intersection with concrete membership *)
Lemma test_intersection_concrete :
    2 ∈ even_nats ∩ small_nats.
Proof.
    apply intersection_characterization_left.
    split.
    - unfold even_nats. exists 1. reflexivity.
    - unfold small_nats. unfold lt. repeat constructor.
Qed.

(* Test 6: Union with concrete membership *)
Lemma test_union_concrete :
    7 ∈ small_nats ∪ large_nats.
Proof.
    apply union_characterization_left.
    right.
    unfold large_nats. unfold ge. repeat constructor.
Qed.

(* Test 7: Intersection elimination and reconstruction *)
Lemma test_intersection_roundtrip :
    forall x, x ∈ even_nats ∩ small_nats -> x ∈ even_nats ∩ small_nats.
Proof.
    intros x h.
    apply intersection_characterization in h.
    apply intersection_characterization_left.
    exact h.
Qed.

(* Test 8: Union elimination and reconstruction *)
Lemma test_union_roundtrip :
    forall x, x ∈ odd_nats ∪ even_nats -> x ∈ odd_nats ∪ even_nats.
Proof.
    intros x h.
    apply union_characterization in h.
    apply union_characterization_left.
    exact h.
Qed.

(* Test 9: Complex intersection property *)
Lemma test_complex_intersection :
    forall x, x ∈ even_nats ∩ small_nats -> x < 5 /\ exists k, x = 2 * k.
Proof.
    intros x h.
    apply intersection_characterization in h.
    destruct h as [heven hsmall].
    split.
    - unfold small_nats in hsmall. exact hsmall.
    - unfold even_nats in heven. exact heven.
Qed.

(* Test 10: Complex union property *)
Lemma test_complex_union :
    1 ∈ odd_nats ∪ large_nats.
Proof.
    apply union_characterization_left.
    left.
    unfold odd_nats.
    exists 0.
    reflexivity.
Qed.
