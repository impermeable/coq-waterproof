Require Import Waterproof.Waterproof.

Goal forall x: nat, 0 = 0.
Proof.
  rwauto.
Qed.

Goal forall x y: nat, forall f: nat -> nat, x = y -> f (S x) = f (S y).
Proof.
  intros.
  assert (x + 1 = y + 1).
  + rewrite H.
    reflexivity.
  + pose proof f_equal.
    rwauto using H1.
Qed.

Goal forall x: nat, 0 = 0.
Proof.
  Fail rwauto using f_equal.
Abort.

(*
  TODO 

  Find a new example showing that the proof search continues in case of fail
*)