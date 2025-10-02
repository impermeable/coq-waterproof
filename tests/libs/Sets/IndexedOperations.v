Require Import Waterproof.Notations.Common.
Require Import Waterproof.Notations.Sets.
Require Import Waterproof.Libs.Sets.IndexedOperations.

Require Import Stdlib.Arith.Arith.
Require Import Stdlib.micromega.Lia.

Open Scope subset_scope.

(* Helper definitions for testing *)
Definition single_element (n : nat) : subset nat := fun x => x = n.
Definition all_nats : subset nat := fun _ => True.
Definition empty_set : subset nat := fun _ => False.

(* Test 1: Basic indexed intersection - element in all sets *)
Lemma test_indexed_intersection_basic :
    5 ∈ indexed_intersection (single_element 0) (fun _ => all_nats).
Proof.
    apply index_intersection_intro.
    intros i hi.
    unfold all_nats.
    exact I.
Qed.

(* Test 2: Indexed intersection elimination *)
Lemma test_index_intersection_elim_usage :
    forall x, x ∈ indexed_intersection (single_element 1) (fun i => single_element i) ->
    x = 1.
Proof.
    intros x h.
    apply index_intersection_elim in h.
    specialize (h 1).
    unfold single_element in h.
    assert (1 = 1) by reflexivity.
    specialize (h H).
    exact h.
Qed.

(* Test 3: Indexed intersection with left elimination *)
Lemma test_index_intersection_elim_left_usage :
    1 ∈ indexed_intersection (single_element 1) (fun i => single_element i).
Proof.
    apply index_intersection_elim_left.
    intros i hi.
    unfold single_element in *.
    rewrite hi.
    reflexivity.
Qed.

(* Test 4: Basic indexed union *)
Lemma test_indexed_union_basic :
    3 ∈ indexed_union (single_element 3) (fun i => single_element i).
Proof.
    apply index_union_elim_left.
    exists 3.
    split.
    - unfold single_element. reflexivity.
    - unfold single_element. reflexivity.
Qed.

(* Test 5: Indexed union with multiple indices *)
Lemma test_indexed_union_multiple :
    2 ∈ indexed_union all_nats (fun i => single_element (i + 2)).
Proof.
    apply index_union_elim_left.
    exists 0.
    split.
    - unfold all_nats. exact I.
    - unfold single_element. reflexivity.
Qed.

(* Test 6: Indexed union elimination *)
Lemma test_index_union_elim_usage :
    forall x, x ∈ indexed_union (single_element 5) (fun i => single_element (i * 2)) ->
    x = 10.
Proof.
    intros x h.
    apply index_union_elim in h.
    destruct h as [i [hi hx]].
    unfold single_element in *.
    rewrite hi in hx.
    exact hx.
Qed.

(* Test 7: Intersection with non-empty index *)
Lemma test_non_empty_intersection :
    1 ∈ indexed_intersection (single_element 0) (fun i : nat => all_nats).
Proof.
    apply index_intersection_intro.
    intros i hi.
    unfold all_nats.
    exact I.
Qed.

(* Test 8: Empty union property *)
Lemma test_empty_index_union :
    forall x, ¬ (x ∈ indexed_union empty_set (fun i : nat => all_nats)).
Proof.
    intros x h.
    apply index_union_elim in h.
    destruct h as [i [hi _]].
    unfold empty_set in hi.
    exact hi.
Qed.

(* Test 9: Single element intersection *)
Lemma test_single_element_intersection :
    7 ∈ indexed_intersection (single_element 0) (fun _ : nat => single_element 7).
Proof.
    apply index_intersection_intro.
    intros i hi.
    unfold single_element.
    reflexivity.
Qed.

(* Test 10: Single element union *)
Lemma test_single_element_union :
    7 ∈ indexed_union (single_element 0) (fun _ : nat => single_element 7).
Proof.
    apply index_union_elim_left.
    exists 0.
    split.
    - unfold single_element. reflexivity.
    - unfold single_element. reflexivity.
Qed.

(* Test 11: Basic intersection property *)
Lemma test_intersection_property :
    forall x, x ∈ indexed_intersection all_nats (fun i : nat => single_element i) ->
    False.
Proof.
    intros x h.
    apply index_intersection_elim in h.
    assert (h0 : 0 ∈ all_nats) by (unfold all_nats; exact I).
    assert (h1 : 1 ∈ all_nats) by (unfold all_nats; exact I).
    assert (eq0 : x = 0) by (apply h; exact h0).
    assert (eq1 : x = 1) by (apply h; exact h1).
    rewrite eq0 in eq1.
    discriminate eq1.
Qed.

(* Test 12: Basic union property *)
Lemma test_union_property :
    forall x, x ∈ indexed_union (single_element 0) (fun _ : nat => single_element x).
Proof.
    intro x.
    apply index_union_elim_left.
    exists 0.
    split.
    - unfold single_element. reflexivity.
    - unfold single_element. reflexivity.
Qed.

(* Test 13: Intersection with constant sets *)
Lemma test_constant_intersection :
    5 ∈ indexed_intersection all_nats (fun _ : nat => single_element 5).
Proof.
    apply index_intersection_intro.
    intros i hi.
    unfold single_element.
    reflexivity.
Qed.

(* Test 14: Union with varying sets *)
Lemma test_varying_union :
    3 ∈ indexed_union (single_element 1) (fun i : nat => single_element (i + 2)).
Proof.
    apply index_union_elim_left.
    exists 1.
    split.
    - unfold single_element. reflexivity.
    - unfold single_element. reflexivity.
Qed.

(* Test 15: Identity property *)
Lemma test_identity_property :
    forall n, n ∈ indexed_union (single_element n) (fun i : nat => single_element i).
Proof.
    intro n.
    apply index_union_elim_left.
    exists n.
    split.
    - unfold single_element. reflexivity.
    - unfold single_element. reflexivity.
Qed.
