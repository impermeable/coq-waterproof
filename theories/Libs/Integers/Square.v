Require Import Waterproof.Notations.Common.
Require Import Waterproof.Notations.Reals.
Require Import Waterproof.Notations.Sets.

Require Import Coq.ZArith.BinInt.

Open Scope subset_scope.
Open Scope Z_scope.

Definition square (n : Z) := n * n.

Definition is_square (n : ℤ) := ∃m ∈ ℤ, square m = n.

Lemma perfect_square_tactic (n m : ℤ) (hp : square n = m) : is_square m.
Proof.
    exists n.
    split; [unfold subset_in; unfold conv; trivial |].
    exact hp.
Qed.