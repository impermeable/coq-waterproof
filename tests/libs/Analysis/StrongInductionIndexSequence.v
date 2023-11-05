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
Require Import Waterproof.Libs.Analysis.StrongInductionIndexSequence.

Variable P : nat -> Prop.


(* Test 1: without other Waterproof tactics. *)
Goal (exists n : nat -> nat, is_index_seq n /\ forall k : nat, P (n k)).
Proof.
  Define the index sequence n inductively.
  - pose (n0 := 0); exists n0.
    admit.
  - Take k : ℕ and assume n(0), ..., n(k) are defined.
    intros H1 H2.
    pose (n_kplus1 := 0); exists n_kplus1.
    split.
    + admit.
    + admit.
Abort.


(* Test 2: with other Waterproof tactics. *)
Require Import Waterproof.Tactics.
Goal (exists n : nat -> nat, is_index_seq n /\ forall k : nat, P (n k)).
Proof.
  Define the index sequence n inductively.
  - Choose n0 := 0.
    admit.
  - Take k : ℕ and assume n(0), ..., n(k) are defined.
    Assume that (forall l : nat, l <= k -> P (n l)).
    Assume that (forall l : nat, l < k -> n l < n (l + 1)).
    Choose n_kplus1 := 0.
    We show both statements.
    + We need to show that (P n_kplus1).
      admit.
    + We need to show that (n k < n_kplus1).
      admit.
Abort.