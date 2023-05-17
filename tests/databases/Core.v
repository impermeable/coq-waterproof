Require Import Waterproof.Waterproof.
Require Import Waterproof.Databases.
Require Import Waterproof.Hints.

Dataset import Core.

Goal forall x: nat, 0 = 0.
Proof.
  wauto.
Qed.

Goal forall x y: nat, forall f: nat -> nat, x = y -> f (S x) = f (S y).
Proof.
  wauto.
Qed.