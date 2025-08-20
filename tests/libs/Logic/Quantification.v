Require Import Waterproof.Tactics.
Require Import Waterproof.Notations.Common.
Require Import Waterproof.Notations.Sets.
Require Import Waterproof.Automation.
Require Import Waterproof.Libs.Logic.Quantification.

Waterproof Enable Automation RealsAndIntegers.

Open Scope subset_scope.

(* Test 1: Basic characterization with simple property *)
Lemma test_unique_exists_characterization {T : Type} (U : subset T) (P : T -> Prop) : 
    (∃! x ∈ U, P x) ↔ (∃ x ∈ U, P x ∧ ∀ y ∈ U, P y ⇒ y = x).
Proof.
    exact (alternative_char_unique_exists U P).
Qed.

(* Test 2: Forward direction of the characterization *)
Lemma test_forward_direction {T : Type} (U : subset T) (P : T -> Prop) :
    (∃! x ∈ U, P x) ⇒ (∃ x ∈ U, P x ∧ ∀ y ∈ U, P y ⇒ y = x).
Proof.
    intro h.
    apply (alternative_char_unique_exists U P).
    exact h.
Qed.

(* Test 3: Backward direction of the characterization *)
Lemma test_backward_direction {T : Type} (U : subset T) (P : T -> Prop) :
    (∃ x ∈ U, P x ∧ ∀ y ∈ U, P y ⇒ y = x) ⇒ (∃! x ∈ U, P x).
Proof.
    intro h.
    apply (alternative_char_unique_exists U P).
    exact h.
Qed.

(* Test 4: Applying to a specific subset with equality property *)
Lemma test_with_specific_property {T : Type} (U : subset T) (a : T) (ha : a ∈ U) : 
    (∃! x ∈ U, x = a) ↔ (∃ x ∈ U, (x = a) ∧ ∀ y ∈ U, (y = a) ⇒ y = x).
Proof.
    exact (alternative_char_unique_exists U (fun x => x = a)).
Qed.

(* Test 5: Simple application showing the lemma works *)
Lemma test_simple_application {T : Type} (U : subset T) (P : T -> Prop) :
    (∃! x ∈ U, P x) ⇒ (∃ x ∈ U, P x).
Proof.
    intro h.
    apply (alternative_char_unique_exists U P) in h.
    destruct h as [x [hx [hp _]]].
    exists x.
    split.
    exact hx.
    exact hp.
Qed.
