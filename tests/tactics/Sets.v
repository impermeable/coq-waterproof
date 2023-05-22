Require Import Ltac2.Ltac2.

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

Require Import Waterproof.Waterproof.
Require Import Waterproof.Automation.
Require Import Waterproof.Notations.
Require Import Waterproof.Tactics.

Local Parameter U : Type.
Local Parameter A B : (Ensemble U).

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
