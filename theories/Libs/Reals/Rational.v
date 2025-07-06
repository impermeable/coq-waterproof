Require Import Notations.Common.
Require Import Notations.Sets.
Require Import Notations.Reals.

Require Import Coq.Reals.Reals.

Open Scope R_scope.

Lemma rational_tactic (q : ℝ) (n m : ℤ) : 0 ≠ m ∧ q = n/m ⇒ q is rational.
Proof.
    intros [h1 h2].
    exists n.
    split.
    unfold conv; unfold subset_in; trivial.
    unfold seal.
    exists m.
    split.
    unfold conv; unfold subset_in; trivial.
    split.
    exact h1.
    exact h2.
Qed.