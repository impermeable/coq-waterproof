Require Import Waterproof.Waterproof.
Require Import Waterproof.Automation.
Require Import Waterproof.Waterprove.

Waterproof Enable Automation Empty.

Goal 0 = 0.
Proof.
  Fail waterprove 5 false [] Positive.
Abort.

Goal forall x y: nat, forall f: nat -> nat, x = y -> f (S x) = f (S y).
Proof.
  Fail waterprove 5 false [] Positive.
Abort.