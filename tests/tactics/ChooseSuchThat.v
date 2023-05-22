Require Import Ltac2.Ltac2.
Require Import Ltac2.Message.

Require Import Rbase.
Require Import Qreals.
Require Import Rfunctions.
Require Import SeqSeries.
Require Import Rtrigo.
Require Import Ranalysis.
Require Import Integration.
Require Import micromega.Lra.
Require Import Max.

Require Import Waterproof.Waterproof.
Require Import Waterproof.Automation.
Require Import Waterproof.Tactics.
Require Import Waterproof.Util.Assertions.

(** Test 0: with labeling *)
Goal (exists n : nat, n + 1 = n)%nat -> False.
Proof.
  intro i.
  Obtain n according to (i), so for n : nat it holds that (n + 1 = n)%nat (ii).
Abort.

(** Test 1: without labeling *)
Goal (exists n : nat, n + 1 = n)%nat -> False.
Proof.
  intro i.
  Obtain n according to (i), so for n : nat it holds that (n + 1 = n)%nat.
Abort.

(** Test 2: wrong type variable *)
Goal (exists n : nat, n + 1 = n)%nat -> False.
Proof.
  intro i.
  Fail Obtain n3 according to (i), so for n3 : bool it holds that (n3 + 1 = n3)%nat.
Abort.

(** Test 3: wrong property *)
Goal (exists n : nat, n + 1 = n)%nat -> False.
Proof.
  intro i.
  Fail Obtain n4 according to (i), so for n4 : nat it holds that (n4 + 1 = n4 + 1)%nat.
Abort.

(** Test 4: whether statement of existence hypothesis is replecated *)
Goal (exists n : nat, n + 1 = n)%nat -> False.
Proof.
  intro i.
  Obtain n according to (i), so for n : nat it holds that (n + 1 = n)%nat.
Abort.

(** Test 5: tactic also works for destructing sig types *)
Goal {n : nat | (n + 1 = n)%nat} -> False.
Proof.
  intro i.
  Obtain n according to (i), so for n : nat it holds that (n + 1 = n)%nat.
Abort.

(** Test 6: whether original hypothesis is destructed, so if the goal depends on the 
      specific term of the sigma type, the goal changes as well.
      As one would expect when using 'destruct .. as [.. ..]'. *)
Goal forall p : {n : nat | (n + 1 = n)%nat}, (proj1_sig p = 0)%nat.
Proof.
  intro p.
  Obtain n according to (p), so for n : nat it holds that (n + 1 = n)%nat (ii).
  simpl.
  assert_goal_is constr:((n = 0)%nat).
Abort.




(** Test 7: more advanced use of the [Obtain...such that...] in the context of limits of sequences *)
Local Open Scope R_scope.

Definition evt_eq_sequences (a b : nat -> R) := (exists k : nat, forall n : nat, (n >= k)%nat -> a n = b n).

Goal forall (a b : nat -> R) (l : R), evt_eq_sequences a b -> (Un_cv a l) -> (Un_cv b l).
Proof.
    intros.
    intro.
    intro.
    pose (H0 eps H1) as i.
    Fail Obtain N1 according to (i), so for N1 : nat it holds that
           (forall n : nat, (n >= N1)%nat -> R_dist (a n) l < eps) (i).
    Obtain N1 according to (i), so for N1 : nat it holds that
           (forall n : nat, (n >= N1)%nat -> R_dist (a n) l < eps).
Abort.
