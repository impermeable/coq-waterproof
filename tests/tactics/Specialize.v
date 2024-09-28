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

(** Test 0: This should be the expected behavior. *)
Goal (forall n : nat, n = n) -> True.
Proof.
intro H.
Use n := 3 in (H).
It holds that (3 = 3).
Abort.

(** Test 1: This should fail as the wrong variable name is chosen. *)
Goal (forall n : nat, n = n) -> True.
Proof.
intro H.
Fail Use m := (3) in (H).
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
Use n := (5) in (F_identity).
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
Use n := 3 in (H).
ltac1:(rename H into HH).   (* test for hypohtesis without producing output *)
Abort.

(** Test 6: multiple variable specifications  *)
Goal (forall n m : nat, n = m) -> False.
Proof.
intro H.
Use n := 3, m := 4 in (H).
It holds that (3 = 4).
Abort.

(** Test 7: multiple variable specifications, different order  *)
Goal (forall n m : nat, n = m) -> False.
Proof.
intro H.
Use m := 4, n := 3 in (H).
Fail It holds that (4 = 3). (* as expected :) *)
It holds that (3 = 4).
Abort.

(* -------------------------------------------------------------------------- *)

Waterproof Enable Redirect Feedback.

(** Test 8 : use a placeholder as variable name *)
Goal (forall a b c : nat, a + b + c = 0) -> False.
Proof.
intro H.
assert_feedback_with_string (fun () => Use b := _ in (H)) Warning
"Please come back to this line later to make a definite choice for b.".
It holds that (forall a c : nat, a + ?b + c = 0) (i).
Abort.

(** Test 8 : use multiple placeholders as variable names *)
Goal (forall a b c : nat, a + b + c = 0) -> False.
Proof.
intro H.
assert_feedback_with_string (fun () => Use a := _, b := _, c := _ in (H)) Warning
"Please come back to this line later to make a definite choice for a, b, c.".
It holds that (?a + ?b + ?c = 0).
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
It holds that (forall b : nat, ?e + ?a + b = 0) (i).
Abort.

(** Test 12 : use an earlier introduced evar *)
Goal (forall a b : nat, a + b = 0) -> False.
Proof.
intro H.
Use a := _ in (H).
It holds that (forall b : nat, ?a + b = 0) (i).
Use b := ?a in (i).
It holds that (?a + ?a = 0).
Abort.

(** Test 13 : TODO: illustration of slightly strange behavior *)

Goal (forall n : nat, f n = n) -> True.
Proof.
intro H.
set (n := 2). (* This renames the binder *)
Fail Use n0 := 5 in (H).
Abort.

Require Import Waterproof.Notations.Sets.

Local Parameter A : nat -> Prop.
Definition B := as_subset _ A.

Local Parameter C : nat -> Prop.
Definition D := as_subset _ C.

(** Test 14 : Specialize a variable in a set. *)
Goal (forall n : nat, n ∈ B -> n = 0) -> True.
Proof.
intro H.
Use n := 3 in (H).
* We need to show that (3 ∈ B).
  Control.shelve ().
* It holds that (3 = 0).
Abort.

(** Test 15 : Choose a blank for a variable in a set *)
Goal (forall x : nat, x ∈ B -> x = 0) -> True.
Proof.
intro H.
assert_feedback_with_strings (fun () => Use x := _ in (H)) Warning
["Please come back to this line later to make a definite choice for x."].
* We need to show that (?x ∈ B).
  Control.shelve ().
* It holds that (?x = 0).
Abort.

(** Test 16 : Specialize variables in a long statements
  with multiple implications *)
Goal (forall x : nat, x ∈ B -> 9 = 9 -> 3 = 3 ->
  True -> forall y : nat, x ∈ B -> 2 = 2 -> 1 = 1 ->
  forall z : nat, z ∈ D -> x = y + z) -> True.
Proof.
intro H.
Use y := 5 in (H).
It holds that (∀ x ∈ B,
  9 = 9 -> 3 = 3 -> True -> x ∈ B -> 2 = 2 -> 1 = 1 -> ∀ z ∈ D,
  x = 5 + z).
Abort.

(** Test 17 : Specialize variables in a long statements
  with multiple implications *)
Goal (forall x : nat, x ∈ B -> 9 = 9 -> 3 = 3 ->
  True -> forall y : nat, x ∈ B -> 2 = 2 -> 1 = 1 ->
  forall z : nat, z ∈ D -> x = y + z) -> True.
Proof.
intro H.
Use x := 2, y := 3, z := 5 in (H).
* We need to show that (2 ∈ B).
  Control.shelve ().
* We need to show that (5 ∈ D).
  Control.shelve ().
* It holds that (9 = 9 -> 3 = 3 -> True ->
    2 ∈ B -> 2 = 2 -> 1 = 1 -> 2 = 3 + 5).
Abort.

(** Test 18 : Specialize variables with blanks in a long statements
  with multiple implications *)
Goal (forall x : nat, x ∈ B -> 9 = 9 -> 3 = 3 ->
  True -> forall y : nat, x ∈ B -> 2 = 2 -> 1 = 1 ->
  forall z : nat, z ∈ D -> x = y + z) -> True.
Proof.
intro H.
assert_feedback_with_strings (fun () => Use x := _, y := _, z := _ in (H))
  Warning
["Please come back to this line later to make a definite choice for x, y, z."].
* We need to show that (?x ∈ B).
  Control.shelve ().
* We need to show that (?z ∈ D).
  Control.shelve ().
* It holds that (9 = 9 -> 3 = 3 -> True ->
    ?x ∈ B -> 2 = 2 -> 1 = 1 -> ?x = ?y + ?z).
Abort.

(** Test 19: have a set that depends on an earlier set*)
Goal (forall x : nat, x ∈ B -> forall y : nat,
  y ∈ as_subset _ (fun z => z > x) -> True) -> True.
Proof.
intro H.
Use x := 2, y := 3 in (H).
* We need to show that (2 ∈ B).
  Control.shelve ().
* We need to show that (3 ∈ as_subset _ (fun z => z > 2) ).
  Control.shelve ().
* It holds that (True).
Abort.

(** Test 20 : Test that things still work if the code for dealing with sets
  throws an exception *)

Local Ltac2 Type exn ::= [OnPurposeExn].
Ltac2 Set test_insertion := fun () => Control.zero (OnPurposeExn).

Goal (forall x : nat, x ∈ B -> 9 = 9 -> 3 = 3 ->
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

Ltac2 Set test_insertion := fun () => ().

(** Test 21 : Test that things still work if binder names get shielded *)

Goal (forall x : nat, x ∈ B -> True) -> True.
Proof.
intro H.
set (x := 2).
Use x := 4 in (H).
* We need to show that (4 ∈ B).
  Control.shelve ().
* It holds that (True).
Abort.

(** Test 21 : Test that things still work if binder names get shielded
    for multiple variables *)

Goal (forall x : nat, x ∈ B -> forall x0 : nat, x0 ∈ D ->
  1 = 1 -> forall x1 : nat, x1 ∈ B -> x = x0 + x1) -> True.
Proof.
intro H.
set (x := 2).
set (x0 := 3).
set (x1 := 4).
Use x := 5, x0 := 6, x1 := 7 in (H).
* We need to show that (5 ∈ B).
  Control.shelve ().
* We need to show that (6 ∈ D).
  Control.shelve ().
* We need to show that (7 ∈ B).
  Control.shelve ().
* It holds that (1 = 1 -> 5 = 6 + 7).
Abort.

(** Test 21 : Test that things still work if binder names get shielded
    but the way they are named is in a strange order *)

Goal (forall x1 : nat, x1 ∈ B -> forall x0 : nat, x0 ∈ D ->
  1 = 1 -> forall x : nat, x ∈ B -> x = x0 + x1) -> True.
Proof.
intro H.
set (x := 2).
set (x0 := 3).
set (x1 := 4).
Use x := 5, x0 := 6, x1 := 7 in (H).
* We need to show that (7 ∈ B).
  Control.shelve ().
* We need to show that (6 ∈ D).
  Control.shelve ().
* We need to show that (5 ∈ B).
  Control.shelve ().
* It holds that (1 = 1 -> 5 = 6 + 7).
Abort.

