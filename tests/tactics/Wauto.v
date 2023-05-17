Require Import Waterproof.Waterproof.

Goal forall x: nat, 0 = 0.
Proof.
  wauto.
Qed.

Goal forall x y: nat, forall f: nat -> nat, x = y -> f (S x) = f (S y).
Proof.
  intros.
  assert (x + 1 = y + 1).
  + rewrite H.
    reflexivity.
  + pose proof f_equal.
    wauto using H1.
Qed.