Require Import Waterproof.Notations.Common.
Require Import Waterproof.Notations.Reals.
Require Import Waterproof.Notations.Sets.

Require Import Stdlib.ZArith.BinInt.

Open Scope subset_scope.
Open Scope Z_scope.

Definition square (n : Z) := n * n.

Definition is_square (n : ℤ) := ∃ m ∈ ℤ, m * m = n.

Lemma perfect_square_of (n m : ℤ) (hp : n * n = m) : is_square m.
Proof.
    exists n.
    split; [unfold subset_in; unfold conv; trivial |].
    exact hp.
Qed.
