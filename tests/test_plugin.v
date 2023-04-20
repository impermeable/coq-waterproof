Require Import Waterproof.Waterproof.

Require Import Reals.

Open Scope R_scope.

hello.

#[export] Hint Resolve f_equal : core.

Goal forall x y: R, forall f: R -> R, x = y -> f (x + 1)= f (y + 1).
Proof.
  intros.
  assert (x + 1 = y + 1).
  + admit.
  + tactid P.
Qed.