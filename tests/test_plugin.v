Require Import Waterproof.Waterproof.
Require Import Waterproof.Databases.

Require Import Reals.

Open Scope R_scope.

Database loaded.
Database load core.
Database loaded.

Database load zarith.
Database loaded.
Database unload core.
Database loaded.

Goal forall x: R, 0 = 0.
Proof.
  pose proof (0 = 0).
  wauto.
Qed.

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

#[export] Hint Resolve f_equal : core.

Goal forall x y: R, forall f: R -> R, x = y -> f (x + 1)= f (y + 1).
Proof.
  intros.
  assert (x + 1 = y + 1).
  + wauto.
    rewrite H.
    reflexivity.
  + wauto.
Qed.