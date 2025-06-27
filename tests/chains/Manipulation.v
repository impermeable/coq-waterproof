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

From Stdlib Require Import Reals.Reals.
From Stdlib Require Import Lra.

Require Import Waterproof.Automation.
Require Import Waterproof.Notations.
Require Import Waterproof.Tactics.

Open Scope R_scope.
Open Scope subset_scope.

(** Test 0: Go from a chain of inequalities to the statement *)
Goal forall x : R, (& x < 4 <= 5 = 2 + 3 < 10) -> (x < 10).
  ltac2: intro x.
  ltac2: intro H.
  Fail ltac2: ltac1:(lra). (* at this stage, lra does not work yet *)
  ltac2: simpl_ineq_chains ().
  ltac2: ltac1:(lra).
Qed.

Goal forall X : Type, forall (a b c d e f g h : X),
  (& a = b = c) -> (& c = d = e = f) -> (& f = g = h) -> a = h.
  ltac2: intro X.
  ltac2: intros a b c d e f g h.
  ltac2: intros chain_1 chain_2 chain_3.
  Fail ltac2: ltac1:(congruence). (* at this stage, congruence does not work yet *)
  ltac2: simpl_ineq_chains ().
  Fail ltac2: ltac1:(congruence). (* at this stage, congruence still does not work *)
  ltac2: split_conjunctions ().
  ltac2: ltac1:(congruence). (* now congruence should work *)
Qed.

Waterproof Enable Automation RealsAndIntegers.

Goal forall x: R, x ∈ [0, 4] -> 0 <= x.
Proof.
  Take x: R.
  Assume that (x ∈ [0, 4]).
  We conclude that (0 <= x).
Qed.

Goal 2 ∈ [0, 4].
Proof.
  We conclude that (2 ∈ [0, 4]).
Qed.
