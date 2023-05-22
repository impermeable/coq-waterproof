Require Import Ltac2.Ltac2.

Require Import Coq.Reals.Reals.
Require Import micromega.Lra.

Require Import Waterproof.Notations.
Require Import Waterproof.Tactics.

Open Scope R_scope.

(** Test 0: Go from a chain of inequalities to the statement *)
Goal forall x : R, (& x < 4 <= 5 = 2 + 3 < 10) -> (x < 10).
  intro x.
  intro H.
  Fail ltac1:(lra). (* at this stage, lra does not work yet *)
  simpl_ineq_chains ().
  ltac1:(lra).
Qed.

Goal forall X : Type, forall (a b c d e f g h : X),
  (& a = b = c) -> (& c = d = e = f) -> (& f = g = h) -> a = h.
  intro X.
  intros a b c d e f g h.
  intros chain_1 chain_2 chain_3.
  Fail ltac1:(congruence). (* at this stage, congruence does not work yet *)
  simpl_ineq_chains ().
  Fail ltac1:(congruence). (* at this stage, congruence still does not work *)
  split_conjunctions ().
  ltac1:(congruence). (* now congruence should work *)
Qed.