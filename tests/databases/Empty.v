Require Import Waterproof.Waterproof.
Require Import Waterproof.Databases.
Require Import Waterproof.Hints.

Dataset import Empty.

Goal 0 = 0.
Proof.
  wauto.
Fail Qed.
Abort.

Goal forall x y: nat, forall f: nat -> nat, x = y -> f (S x) = f (S y).
Proof.
  wauto.
Fail Qed.
Abort.