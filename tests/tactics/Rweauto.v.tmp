Require Import Waterproof.Waterproof.

Goal exists x: nat, x = 0.
Proof.
  rweauto.
Qed.

Goal forall x y: nat, forall f: nat -> nat, x = y -> f (S x) = f (S y).
Proof.
  intros.
  assert (x + 1 = y + 1).
  + rewrite H.
    reflexivity.
  + pose proof f_equal.
    rweauto using H1.
Qed.

Goal forall x: nat, 0 = 0.
Proof.
  Fail rweauto using f_equal.
Abort.

Goal forall x y: nat, forall f: nat -> nat, x = y -> f x = f y /\ y = x.
Proof.
  intros.
  Fail rweauto using Rle_antisym.
  rweauto using f_equal.
Qed.

(*
  TODO 

  Find a new example showing that the proof search continues in case of fail
*)