Require Import Waterproof.Waterproof.
Require Import Waterproof.Databases.

Require Import Reals.Rbase.

Open Scope R_scope.

Dataset loaded.

Dataset import RealsAndIntegers.

Dataset loaded.

Goal forall x: R, 0 = 0.
Proof.
  pose proof (0 = 0).
  wauto.
Qed.

Goal forall x: R, 0 = 0.
Proof.
  pose proof (0 = 0).
  wauto.
Admitted.

Goal forall x y: R, forall f: R -> R, x = y -> f (x + 1)= f (y + 1).
Proof.
  intros.
  assert (x + 1 = y + 1).
  + wauto.
    rewrite H.
    reflexivity.
  + pose proof f_equal.
    wauto.
Qed.

Goal forall x y: R, forall f: R -> R, x = y -> f (x + 1)= f (y + 1).
Proof.
  intros.
  assert (x + 1 = y + 1).
  + wauto.
    rewrite H.
    reflexivity.
  + wauto.
Admitted.

Dataset import RealsAndIntegers.

Goal forall x y: R, forall f: R -> R, x = y -> f (x + 1)= f (y + 1).
Proof.
  intros.
  assert (x + 1 = y + 1).
  + wauto.
    rewrite H.
    reflexivity.
  + wauto.
Qed.