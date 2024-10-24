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
Require Import Waterproof.Notations.Common.
Require Import Waterproof.Notations.Reals.
Require Import Waterproof.Notations.Sets.
Require Import Waterproof.Util.Assertions.

Close Scope R_scope.
Open Scope nat_scope.
Open Scope subset_scope.

#[local] Parameter Q : nat -> Prop.

(* Test 1: without other Waterproof tactics. *)
Goal (∃ n : (nat -> nat), is_index_sequence n /\ ∀ k ∈ nat, Q (n k)).
Proof.
  Define the index sequence n inductively.
  - pose (n_0 := 0); exists n_0.
    Control.shelve ().
  - Take k ∈ ℕ and assume n(0),...,n(k) are defined.
    intros H1 H2.
    pose (n_kplus1 := 0); exists n_kplus1.
    split.
    + Control.shelve ().
    + Control.shelve ().
Abort.

(* Test 2: with other Waterproof tactics. *)
Require Import Waterproof.Tactics.
Goal (∃ n : (nat -> nat), is_index_sequence n /\ ∀ k ∈ nat, Q (n k)).
Proof.
  Define the index sequence n inductively.
  - Choose n_0 := 0.
    + We need to verify that (n_0 ∈ nat).
      Control.shelve ().
    + We need to show that (Q n_0).
      Control.shelve ().
  - Take k ∈ ℕ and assume n(0),...,n(k) are defined.
    Assume that (∀ l ≤ k, Q (n l)).
    Assume that (∀ l < k, n l < n (l + 1)).
    Choose n_kplus1 := 0.
    + We need to verify that (n_kplus1 ∈ nat).
      Control.shelve ().
    + We need to show that (Q(n_kplus1) ∧ n(k) < n_kplus1).
      We show both statements.
      * We need to show that (Q(n_kplus1)).
        Control.shelve ().
      * We need to show that (n k < n_kplus1).
        Control.shelve ().
Abort.



(* Test 3:  more complicated example inspired by actual exercises,
    i.e. with function notation 'n(k)' and 'candy_seq(n(k)) = sweet' as property. *)

Require Import Waterproof.Automation.

Waterproof Enable Automation RealsAndIntegers.
Waterproof Enable Automation Intuition.

Inductive Flavor : Set :=
| sweet : Flavor
| sour  : Flavor
| salty : Flavor.


#[local] Parameter candy_seq : nat → Flavor.
Parameter infinitely_many_sweet : ∀ k : ℕ, ∃ m ≥ k, candy_seq(m) = sweet.

Open Scope subset_scope.

Goal
  (∃ n : (nat → nat), (is_index_sequence n) ∧ (∀ k ∈ ℕ, candy_seq (n k) = sweet)).
Proof.
Define the index sequence n inductively.
- By (infinitely_many_sweet) it holds that
    (∃ m : ℕ, (m ≥ 0)%nat ∧ candy_seq(m) = sweet).
  Obtain such an m.
  Choose n_0 := m.
  + Indeed, (n_0 ∈ ℕ).
  + We conclude that (candy_seq(n_0) = sweet).
- Take k ∈ ℕ and assume n(0),...,n(k) are defined.
  Assume that (∀ l ≤ k, candy_seq(n(l)) = sweet).
  Assume that (∀ l < k, (n(l) < n(l+1))%nat).
  By (infinitely_many_sweet) it holds that
    (∃ m : ℕ, (m ≥ (n k) + 1)%nat ∧ candy_seq(m) = sweet).
  Obtain such an m.
  Choose n_kplus1 := m.
  + Indeed, (n_kplus1 ∈ ℕ).
  + We need to show that (candy_seq(n_kplus1) = sweet ∧ n(k) < n_kplus1).
    We show both statements.
    * We conclude that (candy_seq(n_kplus1) = sweet).
    * We conclude that (n(k) < n_kplus1)%nat.
Qed.

(* Test 4: Test notation in wrapper *)
Goal
  (∃ n : (nat → nat), (is_index_sequence n) ∧ (∀ k ∈ ℕ, candy_seq (n k) = sweet)).
Proof.
Define the index sequence n inductively.
* Control.shelve ().
* let s := Message.to_string (Message.of_constr (Control.goal ())) in
  assert_string_equal s "(Add the following line to the proof:
 * Take k ∈ ℕ and assume n(0),...,n(k) are defined.)".
Abort.
