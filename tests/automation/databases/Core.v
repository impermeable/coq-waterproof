Require Import Waterproof.Waterproof.
Require Import Waterproof.Automation.
Require Import Waterproof.Waterprove.

Waterproof Enable Automation Core.

Goal forall x: nat, 0 = 0.
Proof.
  waterprove 5 false [] Positive.
Qed.

Goal forall x y: nat, forall f: nat -> nat, x = y -> f (S x) = f (S y).
Proof.
  waterprove 5 false [] Positive.
Qed.