(** * Testcases for [set_definitions.v]
Authors: 
    - Jelle Wemmenhove
Creation date: 21 Oct 2021

Testcases for the definitions of subsets of the reals [R], 
and defintions and tests for subsets of a general but fixed set [X].
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

(* Tests for subsets of the reals. *)

(* Test 0: check if we can talk about terms of a subset. *)
Require Import Waterproof.definitions.set_definitions.
Variable B : subset_R.
Variable bb : B.

(* Test 1: check if terms of a subset can be coerced to terms of the underlying set (here: [R]). *)
Require Import Reals.
Open Scope R_scope.
Goal forall b : B, b > 0.
Abort.

(* Test 2: check if we can automatically deduce that for a term of a subset, 
           the characteristic function of that subset hold for that term.  *)
Require Import Waterproof.load_database.Subsets.
Require Import Waterproof.AllTactics.
Goal forall b : B, B b.
  intro b.
  We conclude that (B b).
Qed.

(* Test 3: check the use of a tactic to show the existence of a specific term of a subset. *)
Variable QR : R -> Prop.
Goal exists b0 : B, QR b0.
  It suffices to show that (exists b0 : R, B b0 /\ QR b0).
  Abort.



(** * Preamble for subsets of a generic set X *)

Context (X : Set).

(** The following line automatically generates induction schemes for Records.*)
(*Set Nonrecursive Elimination Schemes. *)
Record     subset_X := mk_subset_X { pred_X :> X -> Prop }.
Record     elements_X (A : subset_X) := mk_elem_X { elem_X :> X; witness_X : A elem_X }.
Definition subset_to_elements_X := fun A : subset_X => elements_X A.
Coercion   subset_to_elements_X : subset_X >-> Sortclass.

Global Hint Resolve witness_X : subsets. (* for all (V : subset_X) (x : V), V x *)

Lemma exists_and_implies_exists_subset_X (A : subset_X) (P : X -> Prop) : 
  (exists a : X, (A a) /\ (P a)) -> (exists a : A, P a).
Proof.
  intro H. destruct H as [a [ainA Ha]]. exists (mk_elem_X A a ainA). exact Ha. 
Defined.
Hint Resolve exists_and_implies_exists_subset_X : subsets.


(* Tests for subsets of the set X *)

(* Test 0: check if we can talk about terms of a subset. *)
Variable C : subset_X.
Variable cc : C.

(* Test 1: check if terms of a subset can be coerced to terms of the underlying set (here: [X]). *)
Variable f : X -> X -> Prop.
Variable x0 : X.
Goal forall c : C, f c x0.
Abort.

(* Test 2: check if we can automatically deduce that for a term of a subset, 
           the characteristic function of that subset hold for that term.  *)
Goal forall c : C, C c.
  intro c.
  We conclude that (C c).
Qed.

(* Test 3: check the use of a tactic to show the existence of a specific term of a subset. *)
Variable QX : X -> Prop.
Goal exists c0 : C, QX c0.
  It suffices to show that (exists c0 : X, C c0 /\ QX c0).
  Abort.
