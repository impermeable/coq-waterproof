Require Import Coq.Reals.Reals.

Require Import Waterproof.Waterproof.
Require Import Waterproof.Automation.
Require Import Waterproof.Waterprove.

Waterproof Enable Automation RealsAndIntegers.

Open Scope R_scope.

Goal forall x y: R, forall f: R -> R, x = y -> f (x + 1) = f (y + 1).
Proof.
  waterprove 5 false [] Positive.
Qed.

Goal forall x y: R, forall f: R -> R, x = y -> f x = f y /\ x = y.
Proof.
  waterprove 5 false [] Positive.
Qed.

Close Scope R_scope.