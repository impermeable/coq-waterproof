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

#[local] Parameter Q : nat -> Prop.


(* Test 1: without other Waterproof tactics. *)
Goal (exists n : nat -> nat, is_index_seq n /\ forall k : nat, Q (n k)).
Proof.
  Define the index sequence n inductively.
  - pose (n_0 := 0); exists n_0.
    admit.
  - Take k : ℕ and assume n(0),...,n(k) are defined.
    intros H1 H2.
    pose (n_kplus1 := 0); exists n_kplus1.
    split.
    + admit.
    + admit.
Abort.


(* Test 2: with other Waterproof tactics. *)
Require Import Waterproof.Tactics.
Goal (exists n : nat -> nat, is_index_seq n /\ forall k : nat, Q (n k)).
Proof.
  Define the index sequence n inductively.
  - Choose n_0 := 0.
    admit.
  - Take k : ℕ and assume n(0),...,n(k) are defined.
    Assume that (forall l : nat, l <= k -> Q (n l)).
    Assume that (forall l : nat, l < k -> n l < n (l + 1)).
    Choose n_kplus1 := 0.
    We show both statements.
    + We need to show that (Q n_kplus1).
      admit.
    + We need to show that (n k < n_kplus1).
      admit.
Abort.



(* Test 3:  more complicated example inspired by actual exercises,
    i.e. with function notation 'n(k)' and 'candy_seq(n(k)) = sweet' as property. *)
Require Import Waterproof.Notations.
Require Import Waterproof.Automation.

Waterproof Enable Automation RealsAndIntegers.
Waterproof Enable Automation Intuition.

Inductive Flavor : Set :=
| sweet : Flavor
| sour  : Flavor
| salty : Flavor.


#[local] Parameter candy_seq : ℕ → Flavor.
Parameter infinitely_many_sweet : ∀ k : ℕ, ∃ m : ℕ, (m ≥ k)%nat ∧ candy_seq(m) = sweet.

Goal
  ∃ n : ℕ → ℕ, (is_index_seq n) ∧ (∀ k : ℕ, candy_seq (n k) = sweet).
Proof.
Define the index sequence n inductively.
- By (infinitely_many_sweet) it holds that
    (∃ m : ℕ, (m ≥ 0)%nat ∧ candy_seq(m) = sweet).
  Obtain such an m.
  Choose n_0 := m.
  We conclude that (candy_seq(n_0) = sweet).
- Take k : ℕ and assume n(0),...,n(k) are defined.
  Assume that (∀ l : ℕ, (l ≤ k)%nat ⇒ candy_seq(n(l)) = sweet).
  Assume that (∀ l : ℕ, (l < k)%nat ⇒ (n(l) < n(l+1))%nat).
  By (infinitely_many_sweet) it holds that
    (∃ m : ℕ, (m ≥ (n k) + 1)%nat ∧ candy_seq(m) = sweet).
  Obtain such an m.
  Choose n_kplus1 := m.
  We show both statements.
  * We conclude that (candy_seq(n_kplus1) = sweet).
  * We conclude that (n(k) < n_kplus1)%nat.
Qed.
