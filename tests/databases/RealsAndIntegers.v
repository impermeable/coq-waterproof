Require Import Waterproof.Waterproof.
Require Import Waterproof.Databases.
Require Import Waterproof.Hints.

Require Import Reals.
Require Import Reals.Reals.

Dataset import RealsAndIntegers.

Open Scope R_scope.

Goal forall x y: R, forall f: R -> R, x = y -> f (x + 1) = f (y + 1).
Proof.
  wauto.
Qed.

Goal forall x y: R, forall f: R -> R, x = y -> f x = f y /\ x = y.
Proof.
  wauto.
Qed.

Close Scope R_scope.