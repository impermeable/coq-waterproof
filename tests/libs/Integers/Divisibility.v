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

Require Import Waterproof.Tactics.
Require Import Waterproof.Notations.Common.
Require Import Waterproof.Notations.Sets.
Require Import Waterproof.Notations.Reals.
Require Import Waterproof.Automation.
Require Import Waterproof.Libs.Integers.Divisibility.

Require Import Coq.ZArith.BinInt.
Require Import Coq.micromega.Lia.

Waterproof Enable Automation RealsAndIntegers.

Open Scope subset_scope.
Open Scope Z_scope.

(* Test 0: Basic divide_char lemma - forward direction *)
Lemma test_divide_char : Z.divide 3 6 ⇒ ∃z ∈ ℤ, 6 = z * 3.
Proof.
    Assume that (Z.divide 3 6).
    By divide_char it holds that (∃z ∈ ℤ, 6 = z * 3).
    We conclude that (∃z ∈ ℤ, 6 = z * 3).
Qed.

(* Test 1: Basic divide_char_inv lemma - reverse direction *)
Lemma test_divide_char_inv : (∃z ∈ ℤ, 12 = z * 4) ⇒ Z.divide 4 12.
Proof.
    Assume that (∃z ∈ ℤ, 12 = z * 4).
    By divide_char_inv it holds that (Z.divide 4 12).
    We conclude that (Z.divide 4 12).
Qed.

(* Test 2: Concrete divisibility example using divide_char *)
Lemma test_concrete_divisibility : Z.divide 5 15.
Proof.
    By divide_char_inv it suffices to show that (∃z ∈ ℤ, 15 = z * 5).
    Choose z := 3.
    { Indeed, z ∈ ℤ. }
    We conclude that (15 = z * 5).
Qed.

(* Test 3: Testing remainder definition with concrete values *)
Lemma test_remainder_17_5_2 : remainder 17 5 2.
Proof.
    apply (remainder_tactic 17 5 2 3).
    reflexivity.
Qed.

(* Test 4: Another remainder example *)
Lemma test_remainder_23_7_2 : remainder 23 7 2.
Proof.
    apply (remainder_tactic 23 7 2 3).
    reflexivity.
Qed.

(* Test 5: Zero divisibility *)
Lemma test_zero_divides_zero : Z.divide 0 0.
Proof.
    By divide_char_inv it suffices to show that (∃z ∈ ℤ, 0 = z * 0).
    Choose z := 1.
    { Indeed, z ∈ ℤ. }
    We conclude that (0 = z * 0).
Qed.

(* Test 6: Every integer divides zero *)
Lemma test_any_divides_zero : ∀ n ∈ ℤ, Z.divide n 0.
Proof.
    Take n ∈ ℤ.
    By divide_char_inv it suffices to show that (∃z ∈ ℤ, 0 = z * n).
    Choose z := 0.
    { Indeed, z ∈ ℤ. }
    We conclude that (0 = z * n).
Qed.

(* Test 7: One divides every integer *)
Lemma test_one_divides_any : ∀ n ∈ ℤ, Z.divide 1 n.
Proof.
    Take n ∈ ℤ.
    By divide_char_inv it suffices to show that (∃z ∈ ℤ, n = z * 1).
    Choose z := n.
    { Indeed, z ∈ ℤ. }
    We conclude that (n = z * 1).
Qed.

(* Test 8: Self-divisibility *)
Lemma test_self_divisibility : ∀ n ∈ ℤ, Z.divide n n.
Proof.
    Take n ∈ ℤ.
    By divide_char_inv it suffices to show that (∃z ∈ ℤ, n = z * n).
    Choose z := 1.
    { Indeed, z ∈ ℤ. }
    We conclude that (n = z * n).
Qed.

(* Test 9: Remainder with unit divisor *)
Lemma test_remainder_unit : remainder 5 1 0.
Proof.
    apply (remainder_tactic 5 1 0 5).
    reflexivity.
Qed.

(* Test 10: Negative number divisibility *)
Lemma test_negative_divisibility : Z.divide (-3) 12.
Proof.
    By divide_char_inv it suffices to show that (∃z ∈ ℤ, 12 = z * (-3)).
    Choose z := (-4).
    { Indeed, z ∈ ℤ. }
    We conclude that (12 = z * (-3)).
Qed.

(* Test 11: Remainder with negative quotient *)
Lemma test_negative_remainder : remainder (-13) 5 2.
Proof.
    apply (remainder_tactic (-13) 5 2 (-3)).
    reflexivity.
Qed.

(* Test 12: Simple divisibility verification *)
Lemma test_simple_divisibility : Z.divide 6 18.
Proof.
    By divide_char_inv it suffices to show that (∃z ∈ ℤ, 18 = z * 6).
    Choose z := 3.
    { Indeed, z ∈ ℤ. }
    We conclude that (18 = z * 6).
Qed.
