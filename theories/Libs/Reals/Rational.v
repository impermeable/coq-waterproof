Require Import Notations.Common.
Require Import Notations.Sets.
Require Import Notations.Reals.

Require Import Coq.Reals.Reals.

Require Import Libs.Reals.Integer.

Open Scope R_scope.
Open Scope subset_scope.

Definition is_rational (q : ℝ) : Prop := ∃n ∈ Z_in_R, ∃m ∈ Z_in_R, 0 ≠ m ∧ q = n/m.

Lemma rational_tactic (q : ℝ) (n m : R) (hn : n ∈ Z_in_R) (hm : m ∈ Z_in_R) 
    : 0 ≠ m ∧ q = n/m ⇒ is_rational q.
Proof.
    intros [h1 h2].
    exists n.
    split.
    exact hn.
    exists m.
    split.
    exact hm.
    split.
    exact h1.
    exact h2.
Qed.