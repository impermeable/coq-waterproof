
Require Import Waterproof.Notations.Common.
Require Import Waterproof.Notations.Reals.
Require Import Waterproof.Notations.Sets.

Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Zeven.

Open Scope subset_scope.
Open Scope Z_scope.

Lemma Zeven_char (n : ℤ) : Zeven n ⇒ ∃m ∈ ℤ, n = 2*m.
Proof.
    rewrite Zeven_ex_iff.
    intros [m h].
    exists m.
    split; [unfold subset_in; unfold conv; trivial |].
    exact h.
Qed.

Lemma Zeven_char_inv (n : ℤ) : (∃m ∈ ℤ, n = 2*m) ⇒ Zeven n.
Proof.
    rewrite Zeven_ex_iff.
    intros [m [_ h]].
    exists m.
    exact h.
Qed.

Lemma Zodd_char (n : ℤ) : Zodd n ⇒ ∃m ∈ ℤ, n = 2*m+1.
Proof.
    rewrite Zodd_ex_iff.
    intros [m h].
    exists m.
    split; [unfold subset_in; unfold conv; trivial |].
    exact h.
Qed.

Lemma Zodd_char_inv (n : ℤ) : (∃m ∈ ℤ, n = 2*m+1) ⇒ Zodd n.
Proof.
    rewrite Zodd_ex_iff.
    intros [m [_ h]].
    exists m.
    exact h.
Qed.

Lemma even_of (n m : ℤ) (hp : 2*n = m) : Zeven m.
Proof.
    rewrite Zeven_ex_iff.
    exists n.
    symmetry.
    exact hp.
Qed.

Lemma odd_of (n m : ℤ) (hp : 2*n + 1 = m) : Zodd m.
Proof.
    rewrite Zodd_ex_iff.
    exists n.
    symmetry.
    exact hp.
Qed.

Lemma even_or_odd (n : ℤ) : Zeven n ∨ Zodd n.
Proof.
    destruct (Zeven_odd_dec n) as [he|ho].
    left; exact he.
    right; exact ho.
Qed.

Lemma not_even_and_odd (n : ℤ) : ¬(Zeven n ∧ Zodd n).
Proof.
    intros [he ho].
    apply (Zeven_not_Zodd n he ho).
Qed.
