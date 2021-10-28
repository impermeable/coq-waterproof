(** * Testcases for [sets_automation_tactics.v]
Authors: 
    - Cosmin Manea (1298542)

Creation date: 09 June 2021

Testcases for the [sets_automation_tactics.v] file.
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

From Ltac2 Require Import Ltac2.
Require Import Sets.Ensembles.
Require Import Sets.Classical_sets.
Require Import Logic.
Require Import ClassicalFacts.
Require Import Sets.Powerset.
Require Import Rbase.
Require Import Qreals.
Require Import Rfunctions.
Require Import SeqSeries.
Require Import Rtrigo.
Require Import Ranalysis.
Require Import Integration.
Require Import micromega.Lra.
Require Import Max.
Require Import Coq.Arith.Wf_nat.
Require Import Waterproof.set_intuition.Enabled.
Require Import Waterproof.set_search_depth.To_5.
Require Import Waterproof.load_database.Sets.


Load sets_automation_tactics.

Variable U : Type.
Variable A B : (Ensemble U).

Open Scope nat.




(** Test 0: U \ U = ∅ *)
Goal (Empty_set U) = (Setminus _ (Full_set U) (Full_set U)).
Proof.
    This set equality is trivial.
Qed.


(** Test 1: U \ ∅ = U *)
Goal (Full_set U) = (Setminus _ (Full_set U) (Empty_set U)).
Proof.
    This set equality is trivial.
Qed.


(** Test 2: A and ∅ are disjoint *)
Goal (Disjoint _ A (Empty_set U)).
Proof.
    This set equality is trivial.
Qed.


(** Test 3: A ∩ B = B ∩ A *)
Goal (Intersection _ A B) = (Intersection _ B A).
Proof.
    This set equality is trivial.
Qed.


(** Test 4: A ∪ B = B ∪ A *)
Goal (Union _ A B) = (Union _ B A).
Proof.
    This set equality is trivial.
Qed.


(** Test 5: ∅ ∩ A = ∅ *)
Goal (Intersection _ (Empty_set U) A) = (Empty_set U).
Proof.
    This set equality is trivial.
Qed.


(** Test 6: U ∩ A = A if A ⊂ U *)
Goal ((Intersection _ (Full_set U) A) = A).
Proof.
    This set equality is trivial.
Qed.


(** Test 7: A = A *)
Goal (A = A).
Proof.
    We prove equality by proving two inclusions.
    This set equality is trivial.
    This set equality is trivial.
Qed.
