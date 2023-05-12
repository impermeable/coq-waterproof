Require Import Waterproof.Waterproof.

Goal exists x: nat, x = 0.
Proof.
  weauto.
Qed.

Goal forall P: nat -> Prop, P 0 -> exists n, P n.
Proof.
  weauto.
Qed.