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

Require Import Waterproof.Tactics.
Require Import Waterproof.Automation.
Require Import Waterproof.Util.Assertions.
Require Import Waterproof.Util.MessagesToUser.
Require Import Waterproof.Notations.Common.

Waterproof Enable Redirect Feedback.

(** Test 0: This should be the expected behavior. *)
Goal (forall n : nat, n = n) -> True.
Proof.
intro H.
Use n := 3 in (H).
It holds that 3 = 3.
Abort.

(** Test 1: This should fail as the wrong variable name is chosen. *)
Goal (forall n : nat, n = n) -> True.
Proof.
intro H.
assert_feedback_with_strings (fun () => Use m := (3) in (H)) Warning
["Expected variable name n instead of m."].
Abort.

(** Test 2: This should fail because the wrong goal is specified. *)
Goal (forall n : nat, n = n) -> True.
Proof.
intro H.
Use n := (3) in (H).
Fail It holds that (True).
Abort.

(** Test 3: This should fail because first the wrapper needs to be resolved. *)
Goal (forall n : nat, n = n) -> True.
Proof.
intro H.
Use n := (3) in (H).
Fail exact I.
Abort.

(** It should be possible to use an outside lemma *)
Local Parameter F : nat -> nat.
Local Parameter F_identity : forall n : nat, F n = n.

Goal True.
Proof.
Fail It holds that (F 3 = 3).
Use n := 5 in F_identity.
It holds that (F 5 = 5).
Abort.

(** Test 4: cannot use specialize tactic for function,
  throw readable error message stating as much.  *)
Definition f : nat -> nat := fun (n : nat) => n.
Goal False.
Proof.
  Fail Use n := 5 in (f).
Abort.

(** Test 5: original universal quantifier hypohtesis left unchanged. *)
Goal (forall n : nat, n = n) -> True.
Proof.
intro H.
Use n := 3 in H.
ltac1:(rename H into HH).   (* test for hypohtesis without producing output *)
Abort.

(** Test 6: multiple variable specifications  *)
Goal (forall n m : nat, n = m) -> False.
Proof.
intro H.
Use n := 3, m := 4 in H.
It holds that (3 = 4).
Abort.

(** Test 7: multiple variable specifications, different order  *)
Goal (forall n m : nat, n = m) -> False.
Proof.
intro H.
assert_feedback_with_strings (fun () => Use m := 4, n := 3 in (H)) Warning
["Expected variable name n instead of m.";
"Expected variable name m instead of n."]. (* as expected :) *)
It holds that (4 = 3).
It holds that (3 = 4).
Abort.

(* -------------------------------------------------------------------------- *)

(* Waterproof Enable Redirect Feedback.*)

(** Test 8 : use a placeholder as variable name *)
Goal (forall a b c : nat, a + b + c = 0) -> False.
Proof.
intro H.
assert_feedback_with_string (fun () => Use a := _ in (H)) Warning
"Please come back to this line later to make a definite choice for a.".
It holds that (forall b c : nat, ?a? + b + c = 0) as (i).
Abort.

(** Test 8 : use multiple placeholders as variable names *)
Goal (forall a b c : nat, a + b + c = 0) -> False.
Proof.
intro H.
assert_feedback_with_string (fun () => Use a := _, b := _, c := _ in (H)) Warning
"Please come back to this line later to make a definite choice for a, b, c.".
It holds that (?a? + ?b? + ?c? = 0).
Abort.

(** Test 9 : use named placeholder: then renaming shouldn't happen *)
Goal (forall a : nat, a = 0) -> False.
Proof.
intro H.
Use a := ?[b] in (H).
Fail It holds that (?a = 0).
Abort.

(** Test 10 : use named placeholder, continue with name of placeholder *)
Goal (forall a : nat, a = 0) -> False.
Proof.
intro H.
Use a := (?[b] : nat) in (H).
It holds that (?b = 0).
Abort.

(** Test 11 : use an already existing evar *)
Goal (forall a b : nat, a + b = 0) -> False.
Proof.
intro H.
ltac1:(evar (e : nat)).
Use a := (?e + _) in (H).
It holds that (forall b : nat, ?e + ?a? + b = 0) as (i).
Abort.

(** Test 12 : use an earlier introduced evar *)
Goal (forall a b : nat, a + b = 0) -> False.
Proof.
intro H.
Use a := _ in (H).
It holds that (forall b : nat, ?a? + b = 0) as (i).
Use b := ?a? in (i).
It holds that (?a? + ?a? = 0).
Abort.

(** Test 13 : TODO: illustration of slightly strange behavior : was fixed with
  version of specialize *)

(* Goal (forall n : nat, f n = n) -> True.
Proof.
intro H.
set (n := 2). (* This renames the binder *)
Fail Use n0 := 5 in (H).
Abort.*)

Require Import Waterproof.Notations.Sets.

Local Parameter A : nat -> Prop.
Definition B := as_subset _ A.

Local Parameter C : nat -> Prop.
Definition D := as_subset _ C.

Open Scope subset_scope.

(** Test 14 : Specialize a variable in a set. *)
Goal (∀ n ∈ B, n = 0) -> True.
Proof.
intro H.
Use n := 3 in (H).
{ We need to verify that (3 ∈ B).
  Control.shelve ().
}
It holds that (3 = 0).
Abort.

(** Test 15 : Choose a blank for a variable in a set *)
Goal (∀ x ∈ B, x = 0) -> True.
Proof.
intro H.
assert_feedback_with_strings (fun () => Use x := _ in (H)) Warning
["Please come back to this line later to make a definite choice for x."].
* We need to verify that (?x? ∈ B).
  Control.shelve ().
* It holds that (?x? = 0).
Abort.

(** Test 16 : Specialize variables in a long statements
  with multiple implications *)
Goal (∀ x ∈ B, 9 = 9 -> 3 = 3 ->
  True -> forall y : nat, x ∈ B -> 2 = 2 -> 1 = 1 ->
  forall z : nat, z ∈ D -> x = y + z) -> True.
Proof.
intro H.
Use x := 5 in (H).
* We need to verify that (5 ∈ B).
  Control.shelve ().
* It holds that (9 = 9 -> 3 = 3 -> True ->
  ∀ y, 5 ∈ B -> 2 = 2 -> 1 = 1 -> ∀ z, z ∈ D -> 5 = y + z).
Abort.

(** Test 17 : Specialize variables in a long statements
  with multiple implications *)
Goal (∀ x ∈ B, ∀ y ∈ D, 2 = 2 -> 1 = 1 ->
  forall z : nat, z ∈ D -> x = y + z) -> True.
Proof.
intro H.
Use x := 2, y := 3 in (H).
* We need to verify that (2 ∈ B).
  Control.shelve ().
* We need to verify that (3 ∈ D).
  Control.shelve ().
* It holds that (2 = 2 -> 1 = 1 ->
    ∀ z, z ∈ D -> 2 = 3 + z).
Abort.

(** Test 18 : Specialize variables with blanks in a long statements
  with multiple implications *)
Goal (∀ x ∈ B, ∀ y : nat, ∀ z ∈ D, 1 = 1 -> x = y + z) -> True.
Proof.
intro H.
assert_feedback_with_strings (fun () => Use x := _, y := _, z := _ in (H))
  Warning
["Please come back to this line later to make a definite choice for x, y, z."].
* We need to verify that (?x? ∈ B).
  Control.shelve ().
* We need to verify that (?z? ∈ D).
  Control.shelve ().
* It holds that (1 = 1 -> ?x? = ?y? + ?z?).
Abort.

(** Test 19: have a set that depends on an earlier set*)
Goal (∀ x ∈ B, ∀ y ∈ as_subset _ (fun z => z > x), True) -> True.
Proof.
intro H.
Use x := 2, y := 3 in (H).
* We need to verify that (2 ∈ B).
  Control.shelve ().
* We need to verify that (3 ∈ as_subset _ (fun z => z > 2) ).
  Control.shelve ().
* It holds that (True).
Abort.

(** Test 20 : Test that things still work if the code for dealing with sets
  throws an exception -- this was useful for different version of the tactic *)

(* Goal (forall x : nat, x ∈ B -> 9 = 9 -> 3 = 3 ->
  True -> forall y : nat, x ∈ B -> 2 = 2 -> 1 = 1 ->
  forall z : nat, z ∈ D -> x = y + z) -> True.
Proof.
intro H.
assert_feedback_with_strings (fun () => Use x := _, y := _, z := _ in (H)) Warning
["Please come back to this line later to make a definite choice for x, y, z.";
"Could not understand the structure with the involved sets. A simplified version of 'Use' is used.
This is a not a problem, but you may report this example, mentioning the exception:
OnPurposeExn"].
It holds that (?x ∈ B ->
9 = 9 ->
3 = 3 -> True -> ?x ∈ B -> 2 = 2 -> 1 = 1 -> ?z ∈ D -> ?x = ?y + ?z).
Abort.

Ltac2 Set test_insertion := fun () => ().*)

(** Test 21 : Test that things still work if binder names get shielded *)

Goal (∀ x ∈ B, True) -> True.
Proof.
intro H.
set (x := 2).
Use x := 4 in (H).
* We need to verify that (4 ∈ B).
  Control.shelve ().
* It holds that (True).
Abort.

(** Test 21 : Test that things still work if binder names get shielded
    for multiple variables *)

Goal (∀ x ∈ B, forall x0 : nat, ∀ x1 ∈ D, x = x0 + x1) -> True.
Proof.
intro H.
set (x := 2).
set (x0 := 3).
set (x1 := 4).
Use x := 5, x0 := 6, x1 := 7 in (H).
* We need to verify that (5 ∈ B).
  Control.shelve ().
* We need to verify that (7 ∈ D).
  Control.shelve ().
* It holds that (5 = 6 + 7).
Abort.

(** Test 22 : immediate verification *)
Goal ∀ y ∈ B, (∀ x ∈ B, x = 0) -> y = 0.
Proof.
Take y ∈ B.
Assume that (∀ x ∈ B, x = 0) as (i).
Use x := y in (i).
* Indeed, (y ∈ B).
* Fail We conclude that (y = 0). (* TODO: fix this? *)
  It holds that (y = 0).
  We conclude that (y = 0).
Qed.

(** Test 23 : Choose a natural number larger than another natural number, but in R_scope. *)

Require Import Coq.Reals.Reals.
Open Scope R_scope.

Goal (∀ y > 0%nat, INR(y) = 0) -> True.
Proof.
intro i.
Use y := 2%nat in (i).
* assert_constr_equal (Control.goal ()) constr:(VerifyGoal.Wrapper (gt 2 0)).
  Indeed, ((2 > 0)%nat).
* It holds that (INR 2 = 0).
  exact I.
Qed.

(** Test 23 : Choose a natural number less than another natural number, but in R_scope. *)

Goal (∀ y < 3%nat, INR(y) = 0) -> True.
Proof.
intro i.
Use y := 2%nat in (i).
* assert_constr_equal (Control.goal ()) constr:(VerifyGoal.Wrapper (lt 2 3)).
  Indeed, ((2 < 3)%nat).
* It holds that (INR 2 = 0).
  exact I.
Qed.

(** Test 24 : Choose a natural number less than another natural number, but in R_scope. *)

Goal (∀ y ≤ 3%nat, INR(y) = 0) -> True.
Proof.
intro i.
Use y := 2%nat in (i).
* assert_constr_equal (Control.goal ()) constr:(VerifyGoal.Wrapper (le 2 3)).
  Indeed, ((2 <= 3)%nat).
* It holds that (INR 2 = 0).
  exact I.
Qed.

(** Test 25 : Test notation in wrapper. *)
Goal (∀ y ≤ 3, y = 0) -> True.
intro i.
Use y := 2 in (i).
let s := Message.to_string (Message.of_constr (Control.goal ())) in
assert_string_equal s (String.concat ""
 ["(Add the following line to the proof:
 ";"
 { Indeed, (2 <= 3). }
 ";"
 or write:
 ";"
 { We need to verify that (2 <= 3).
 ";"
 }
 ";"
 if intermediary proof steps are required.)"]).
Abort.
Close Scope R_scope.

(** Test 26 : The automation shouldn't resolve the evars... *)

Waterproof Enable Automation RealsAndIntegers.

Goal (∀ x > 2, x = 0) -> True.
Proof.
intro i.
Use x := _ in (i).
* Fail Indeed, (?x? > 2).
  We need to verify that (?x? > 2).
  Control.shelve ().
Abort.

(** Test 27 : Fail to close proof is blank is left in proof. *)

Goal (∀ y ≥ 0, True) -> True.
Proof.
  intro H.
  Use y := _ in (H).
  { Indeed, ((?y? >= 0)). }
  It holds that (True).
  We conclude that (True).
  Fail ().  (* No goals remaining. *)
  Fail Qed. (* Cannot close proof. *)
Abort.


(** Test 28: Choose should allow complex expression without parens. *)
Goal (forall n : nat, n = n) -> True.
Proof.
intro H.
Use n := 3 + 1 in H.
It holds that 4 = 4.
Abort.
Close Scope subset_scope.
