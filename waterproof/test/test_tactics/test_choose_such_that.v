(** * Testcases for [choose_such_that.v]
Authors: 
    - Cosmin Manea (1298542)

Creation date: 09 June 2021

Testcases for the [Obtain ... such that ...] tactic.
Tests pass if they can be run without unhandled errors.
--------------------------------------------------------------------------------

This file is part of Waterproof-lib.

Waterproof-lib is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

Waterproof-lib is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with Waterproof-lib.  If not, see <https://www.gnu.org/licenses/>.
*)

From Ltac2 Require Import Ltac2.
Require Import Rbase.
Require Import Qreals.
Require Import Rfunctions.
Require Import SeqSeries.
Require Import Rtrigo.
Require Import Ranalysis.
Require Import Integration.
Require Import micromega.Lra.
Require Import Max.

Require Import Waterproof.test_auxiliary.
Load choose_such_that.

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
  Check (i).
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
