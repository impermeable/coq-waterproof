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

Require Import Waterproof.Waterproof.
Require Import Waterproof.Automation.
Require Import Waterproof.Tactics.
Require Import Waterproof.Util.MessagesToUser.
Require Import Waterproof.Util.Assertions.

(** Test 0: This should work fine *)
Goal forall n : nat, n <= 2*n.
    Take n : nat.
Abort.

Waterproof Enable Redirect Feedback.

(** Test 1: Also this should work fine, but with a warning *)
Goal forall n : nat, n <= 2*n.
    assert_feedback_with_string (fun () => Take x : nat) Warning
"Expected variable name n instead of x.".
Abort.

(** Test 2: This should raise an error, because the type does not match*)
Goal forall n : nat, n <= 2*n.
    Fail Take n : bool.
Abort.

(** Test 3: This should raise an error,
    because [Take] solves forall-quatifiers *)
Goal exists n : nat, n <= 2*n.
    Fail Take n : nat.
Abort.

(** Test 4: Multi argument testcase *)
Goal forall n : nat, forall m : nat, n + m <= 2*n + m.
    Take n : nat and m : nat.
Abort.

(** Test 5: Two sets of multiple variables of the same type. *)
Goal forall (n m k: nat) (b1 b2: bool), Nat.odd (n + m + k) = andb b1 b2.
    Take n, m, k : nat and b1, b2: bool.
Abort.

(** Test 5.1: Too few variables of the same type. *)
Goal forall (n m k: nat) (b1 b2: bool), Nat.odd (n + m + k) = andb b1 b2.
    Take n, m : nat.
Abort.

(** Test 5.2: Too many variables of the same type. *)
Goal forall (n m k: nat) (b1 b2: bool), Nat.odd (n + m + k) = andb b1 b2.
    Fail Take n, m, k, l : nat.
Abort.

(** Test 5.3: Too many variables (of the same type). *)
Goal forall (n m k: nat), Nat.odd (n + m + k) = false.
    Fail Take n, m, k, l : nat.
Abort.

(** Test 5.4: Too many variables (of different types). *)
Goal forall (n m k: nat), Nat.odd (n + m + k) = false.
    Fail Take n, m, k : nat and l : bool.
Abort.

(** Test 6: Two sets of multiple variables of the same type,
    but with different names *)
Goal forall (n m k: nat) (b1 b2: bool), Nat.odd (n + m + k) = andb b1 b2.
    assert_feedback_with_strings
    (fun () => Take a, b, c : nat and d, e: bool) Warning
[
"Expected variable name n instead of a.";
"Expected variable name m instead of b.";
"Expected variable name k instead of c.";
"Expected variable name b1 instead of d.";
"Expected variable name b2 instead of e."].
Abort.

(** Test 7: not allowed to introduce so many bools *)
Goal forall (n m k: nat) (b1 b2: bool), Nat.odd (n + m + k) = andb b1 b2.
    Fail Take a, b, c, d, e : bool.
Abort.

(** Test 8: look how crazy many vars we can introduce*)
Goal forall (a b c d e f g: nat) (b1 b2: bool),
    Nat.odd (a + b + c + d + e + f + g) = andb b1 b2.
    Take a, b, c, d, e, f, g : nat and b1, b2: bool.
Abort.

(** Test 9: This should give a helpful error.
    (Note that two variables have the same name "a"!)

    Currently it raises "Internal (err:(a is already used.))"
    which seems clear enough :)
    *)
Goal forall (a b c d e f g: nat) (b1 b2: bool),
    Nat.odd (a + b + c + d + e + f + g) = andb b1 b2.
    assert_fails_with_string (fun() => Take a, b, c, d, e, f, g : nat and a, h: bool)
"Internal (err:(a is already used.))".
Abort.

(** Test 10: Two sets of multiple variables of the same type.
    But in a *different order* with different names.

    This should raise an error, as the order of introducing variables is different.
*)
Goal forall (n m k: nat)  (b1 b2: bool), Nat.odd (n + m + k) = andb b1 b2.
    Fail Take y, u : bool and a, b, c : nat.
Abort.

(** Test 11: Attempting to show an implication should be rejected. *)
Goal (0 = 1) -> False.
  Fail Take p : (0 = 1).
Abort.

(** Test 12: Attempting to show a negation should be rejected. *)
Goal not (0 = 1).
  Fail Take p : (0 = 1).
Abort.

Require Import Coq.Reals.Reals.
(** Test 13: Introducing too many variables when
    the for all statement is followed by an implication.
*)
Goal forall (n : nat) (x y : R), (0 < x < y)%R -> (x^n < y^n)%R.
Proof.
  Fail Take n : nat and x, y, z : R.
  Fail Take n : nat and x, y : R and f : (R -> R).
  Take n : nat and x, y : R.
Abort.

(** ** Tests about variable names *)

(** Test 14: Warn on using a different variable name *)
Goal forall n : nat, n = n.
  assert_feedback_with_string (fun () => Take m : nat) Warning
"Expected variable name n instead of m.".
Abort.

(** Test 15: Warn on using different variable name, if variable has
    visually been renamed. *)
Goal forall n : nat, n = n.
Proof.
  set (n := 1).
  assert_feedback_with_string (fun () => Take m : nat) Warning
"Expected variable name n0 instead of m.".
Abort.

(** Test 16: Do not warn if variable has visually been renamed (although
    internally, the binder name stays the same) *)
Goal forall n : nat, n = n.
Proof.
  set (n := 1).
  Take n0 : nat. (* This should produce no warning. *)
Abort.

(** Test 17: Warn on using different variable name *)
Goal forall m n : nat, n = m.
Proof.
  assert_feedback_with_string (fun () => Take n : nat) Warning
"Expected variable name m instead of n.".
  assert_no_feedback (fun () => Take n0 : nat) Warning.
Abort.

(** Test 18: Warn on using different variable name *)
Goal forall m n : nat, n = m.
Proof.
  set (m := 3).
  set (n := 4).
  assert_no_feedback (fun () => Take m0 : nat) Warning.
  assert_no_feedback (fun () => Take n0 : nat) Warning.
Abort.

(** Test 19: If a statement reuses a same binder name, and
    variable are introduced one by one, go with the
    visually rename binder. *)
Goal forall n : nat, forall n : nat, n = n.
Proof.
  Take n : nat.
  assert_no_feedback (fun () => Take n0 : nat) Warning.
Abort.

(** Test 20: Fail when twice the same variable is introduced *)
Goal forall n : nat, forall n : nat, n = n.
Proof.
  assert_feedback_with_string (fun () => assert_fails_with_string (fun () => Take n, n : nat)
"Internal (err:(n is already used.))") (*This should produce an error ... *)
Warning
"Expected variable name n0 instead of n.". (* ... and also produce a warning *)
Abort.

(** Test 21: It should be possible to provide fresh variable names
    (although in the expected order) *)
Goal forall n : nat, forall n : nat, n = n.
Proof.
  assert_no_feedback (fun () => Take n, n0 : nat) Warning.
Abort.

(** Test 22: It should be possible to provide fresh variable names
    (although in the expected order) case with 3 variables *)
Goal forall n : nat, forall n : nat, forall n : nat, n = n.
Proof.
  assert_no_feedback (fun () => Take n, n0, n1 : nat) Warning.
Abort.

(** Test 23: It should  be possible to provide fresh variable names
    (although in the expected order), if also already a
    variable has been defined with the same name. *)
Goal forall n : nat, forall n : nat, forall n : nat, n = n.
Proof.
  (set (n := 1)).
  assert_no_feedback (fun () => Take n0, n1, n2 : nat) Warning.
Abort.

Require Import Waterproof.Notations.Sets.

Local Parameter A : nat -> Prop.
Definition B := as_subset _ A.
Local Parameter C : nat -> Prop.
Definition D := as_subset _ C.

(** ** Tests for taking from sets *)
Open Scope subset_scope.
(** Test 24: Take from a set *)
Goal ∀ n ∈ B, n = 0.
  Take n ∈ B.
  assert (n ∈ B) by assumption.
Abort.

(** Test 25, Take multiple variables from a set *)
Goal ∀ k ∈ B, ∀ l ∈ B, ∀ m ∈ B, ∀ n ∈ B, k + l + m + n = 0.
  Take k, l, m, n ∈ B.
  assert (k ∈ B) by assumption.
  assert (l ∈ B) by assumption.
  assert (m ∈ B) by assumption.
  assert (n ∈ B) by assumption.
Abort.

Close Scope subset_scope.

(** Test 26, Take from a set of real numbers *)

Require Import Waterproof.Notations.Reals.
Open Scope R_scope.
Open Scope subset_scope.

Local Parameter a b : R.

Goal ∀ x ∈ [a, b], True.
Proof.
We need to show that (∀ x ∈ [a, b], True).
Take x ∈ [a, b].
Abort.

(** Test 27, Take from a full set *)
Goal ∀ x ∈ ℝ, x > 0.
Take x ∈ ℝ.
Abort.

(** Test 28, Take with double coercion *)

Structure test_structure  := BuildTestStructure { test_carrier :> Type }.
Local Definition V := BuildTestStructure R.

Goal ∀ x ∈ V, x = 0.
Proof.
Take x ∈ V. (* V first gets coerced to Type, then to subset *)
(* To see this, for instance use *)
(* Set Printing Coercions. *)
Abort.

(** Test 29, Take with an inequality in nat, but in R_scope *)
Goal ∀ n > 3%nat, Rplus n n = 0.
Proof.
Take n > 3%nat.
assert_constr_equal (Constr.type (Control.hyp @_H)) constr:(gt n 3).
Abort.

(** Test 30, Take with an lt in nat, but in R_scope *)
Goal ∀ n < 3%nat, INR(n) = 0.
Proof.
Take n < 3%nat.
assert_constr_equal (Constr.type (Control.hyp @_H)) constr:(lt n 3).
Abort.

(** Test 31, Take with an lt in nat, but in R_scope *)
Goal ∀ n ≤ 3%nat, INR(n) = 0.
Proof.
Take n ≤ 3%nat.
assert_constr_equal (Constr.type (Control.hyp @_H)) constr:(le n 3).
Abort.

Waterproof Enable Redirect Errors.

(** Test 32, Use take with the wrong symbol *)
Goal ∀ n > 3, n = 0.
assert_fails_with_string (fun () => Take n < 3)
"The condition (n < 3) does not correspond to the expected condition (n > 3)".
Abort.

(** Test 33, Check that subset type is simplified when using Take with colon *)
Goal ∀ n > 3, n = 0.
Proof.
Take n : R.
assert_constr_equal (Constr.type constr:(n)) constr:(R).
Abort.

(** Test 33, Check that subset type is simplified when using Take with > *)
Goal ∀ n > 3, n = 0.
Proof.
Take n > 3.
assert_constr_equal (Constr.type constr:(n)) constr:(R).
Abort.

(** Test 34, Check that take can be used with complex expression without parens **)
Goal ∀ n > 2 + 1, n = 0.
Proof.
Take n > 2 + 1.
assert_constr_equal (Constr.type constr:(n)) constr:(R).
Abort.

(** Test 35, Check that take can be used with ∈ and complex expression without parens **)

Definition const_nat (_ : nat) : Type := nat.

Goal ∀ m ∈ nat, ∀ n ∈ nat, ∀ k ∈ nat, ∀ l ∈ nat, ∀ j ∈ nat, True.
Proof.
Take m, n ∈ const_nat 0 and k, l ∈ const_nat 1 and j ∈ const_nat 2.
Abort.
