(******************************************************************************)
(*                  This file is part of Waterproof-lib.                      *)
(*                                                                            *)
(*   Waterproof-lib is free software: you can redistribute it and/or modify   *)
(*    it under the terms of the GNU General Public License as published by    *)
(*     the Free Software Foundation, either version 3 of the License, or      *)
(*                    (at your option) any later version.                     *)
(*                                                                            *)
(*     Waterproof-lib is distributed in the hope that it will be useful,      *)
(*      but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*       MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the         *)
(*               GNU General Public License for more details.                 *)
(*                                                                            *)
(*     You should have received a copy of the GNU General Public License      *)
(*   along with Waterproof-lib. If not, see <https://www.gnu.org/licenses/>.  *)
(*                                                                            *)
(******************************************************************************)

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

(** Test 0: works with existence statement*)
Goal (exists n : nat, n + 1 = n)%nat -> False.
Proof.
  intro H.
  Obtain such an n.
Abort.

(** Test 1: works with sigma type *)
Goal {n : nat | (n + 1 = n)%nat} -> False.
Proof.
  intro H.
  Obtain such an n.
Abort.

(** Test 2: Fails with other type. *)
Goal (exists n : nat, n + 1 = n)%nat -> (0 = 0) -> False.
Proof.
  intros H1 H2.
  Fail Obtain such an n.
Abort.

(** Test 3: Fails when variable name is already in use. *)
Goal forall m : nat, (exists n : nat, n + 1 = m)%nat -> False.
Proof.
  intros m H.
  Fail Obtain such an m.
Abort.

(** Test 4: existence statement is replaced by copy with the same label. *)
Goal (exists n : nat, n + 1 = n)%nat -> False.
Proof.
  intro i.
  Obtain such an n. (* check for yourself! *)
Abort.


(** Test 5: whether original hypothesis is destructed, so if the goal depends on the 
      specific term of the sigma type, the goal changes as well.
      As one would expect when using 'destruct .. as [.. ..]'. *)
Goal forall p : {n : nat | (n + 1 = n)%nat}, (proj1_sig p = 0)%nat.
Proof.
  intro p.
  Obtain such an n.
  We need to show that (n = 0)%nat.
  assert_goal_is constr:((n = 0)%nat).
Abort.

(** Test 6: works with specifying statement.  *)
Goal (exists n : nat, n + 1 = n)%nat -> False.
Proof.
  intro i.
  Obtain n according to (i).
Abort.

(** Test 7: fails if specified statement does not exist.  *)
Goal (exists n : nat, n + 1 = n)%nat -> False.
Proof.
  intro i.
  Fail Obtain n according to (ii).
Abort.


(** Test 8: more advanced use of the [Obtain...such that...] in the context of limits of sequences *)
Local Open Scope R_scope.

Definition evt_eq_sequences (a b : nat -> R) := (exists k : nat, forall n : nat, (n >= k)%nat -> a n = b n).

Goal forall (a b : nat -> R) (l : R), evt_eq_sequences a b -> (Un_cv a l) -> (Un_cv b l).
Proof.
    intros.
    intro.
    intro.
    pose (H0 eps H1).
    Obtain such an N1.
Abort.