Require Import Waterproof.Notations.Common.
Require Import Waterproof.Notations.Reals.
Require Import Waterproof.Notations.Sets.

Require Import Stdlib.ZArith.BinInt.

Open Scope subset_scope.
Open Scope Z_scope.

Lemma divide_char (x y : ℤ) : Z.divide x y ⇒ ∃ z ∈ ℤ, y = z*x.
Proof.
    intros [z hz].
    exists z.
    split; [unfold subset_in; unfold conv; trivial| ].
    exact hz.
Qed.

Lemma divide_char_inv (x y : ℤ) : (∃ z ∈ ℤ, y = z*x) ⇒ Z.divide x y.
Proof.
    intros [z [_ hz]].
    exists z.
    exact hz.
Qed.

Definition remainder (n q r : ℤ) : Prop := ∃ m ∈ ℤ, n = q * m + r.

Lemma remainder_of (n q r m : ℤ) (h : n = q * m + r) : remainder n q r.
Proof.
    exists m.
    split.
    unfold conv; unfold subset_in; trivial.
    exact h.
Qed.
