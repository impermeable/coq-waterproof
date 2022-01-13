(** * Testcases for [choose_such_that.v]
Authors: 
    - Cosmin Manea (1298542)

Creation date: 09 June 2021

Testcases for the [Choose ... such that ...] tactic.
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


(** Test 0: introducing a variable in an exists definition *)
Goal forall n : nat, n = n.
Proof.
    assert (forall n : nat, exists m : nat, forall t : nat, (n = m)) as X.
    {
        intro n.
        pose (m := n); exists m.
        intro t.
        reflexivity.
    }
    intro n.
    pose (X n) as i.
    Choose m such that sample_name according to (i).
Abort.


(** Test 1: more advanced use of the [Choose...such that...] in the context of limits of sequences *)
Local Open Scope R_scope.




Definition evt_eq_sequences (a b : nat -> R) := (exists k : nat, forall n : nat, (n >= k)%nat -> a n = b n).

Goal forall (a b : nat -> R) (l : R), evt_eq_sequences a b -> (Un_cv a l) -> (Un_cv b l).
Proof.
    intros.
    intro.
    intro.
    pose (H0 eps H1) as i.
    Choose n1 such that a_close_to_l according to (i).
Abort.
