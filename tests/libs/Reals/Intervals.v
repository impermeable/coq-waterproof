Require Import Waterproof.Notations.Common.
Require Import Waterproof.Notations.Sets.
Require Import Waterproof.Notations.Reals.
Require Import Waterproof.Libs.Reals.Intervals.

Require Import Coq.Reals.Reals.

Open Scope R_scope.

(* Test 1: Proof that a closed interval [0, 1] is an interval *)
Lemma test_closed_interval_01 : is_interval [0, 1].
Proof.
    apply (Closed [0, 1] 0 1).
    reflexivity.
Qed.

(* Test 2: Proof that a closed-open interval [0, 1) is an interval *)
Lemma test_closed_open_interval_01 : is_interval [0, 1).
Proof.
    apply (Closed_Open [0, 1) 0 1).
    reflexivity.
Qed.

(* Test 3: Proof for a closed interval with different bounds *)
Lemma test_closed_interval_neg2_5 : is_interval [-2, 5].
Proof.
    apply (Closed [-2, 5] (-2) 5).
    reflexivity.
Qed.

(* Test 4: Proof for a closed-open interval with negative bounds *)
Lemma test_closed_open_interval_neg3_0 : is_interval [-3, 0).
Proof.
    apply (Closed_Open [-3, 0) (-3) 0).
    reflexivity.
Qed.

(* Test 5: Generic proof showing any closed interval is an interval *)
Lemma test_generic_closed_interval (a b : ℝ) : is_interval [a, b].
Proof.
    apply (Closed [a, b] a b).
    reflexivity.
Qed.

(* Test 6: Generic proof showing any closed-open interval is an interval *)
Lemma test_generic_closed_open_interval (a b : ℝ) : is_interval [a, b).
Proof.
    apply (Closed_Open [a, b) a b).
    reflexivity.
Qed.

(* Test 7: Proof that a degenerate closed interval is an interval *)
Lemma test_degenerate_closed_interval : is_interval [3, 3].
Proof.
    apply (Closed [3, 3] 3 3).
    reflexivity.
Qed.

(* Test 8: Proof demonstrating interval with zero as endpoint *)
Lemma test_interval_with_zero : is_interval [0, 10].
Proof.
    apply (Closed [0, 10] 0 10).
    reflexivity.
Qed.

(* Test 9: Proof demonstrating closed interval with large negative bounds *)
Lemma test_large_negative_interval : is_interval [-100, -50].
Proof.
    apply (Closed [-100, -50] (-100) (-50)).
    reflexivity.
Qed.

(* Test 10: Proof for closed-open interval with fractional endpoints *)
Lemma test_closed_open_fractional : is_interval [1/2, 2).
Proof.
    apply (Closed_Open [1/2, 2) (1/2) 2).
    reflexivity.
Qed.

(* Test 11: Proof for closed interval with equal bounds (unit interval) *)
Lemma test_unit_interval : is_interval [0, 1].
Proof.
    apply (Closed [0, 1] 0 1).
    reflexivity.
Qed.

(* Test 12: Proof demonstrating closed interval spanning negative to positive *)
Lemma test_spanning_interval : is_interval [-10, 10].
Proof.
    apply (Closed [-10, 10] (-10) 10).
    reflexivity.
Qed.

(* Attempt to prove open interval using alternative notation *)
Definition open_interval (a b : ℝ) : subset ℝ := as_subset ℝ (fun x => a < x < b).

(* Test 13: Proof that an explicitly defined open interval is an interval *)
Lemma test_explicit_open_interval : is_interval (open_interval 0 1).
Proof.
    apply (Open (open_interval 0 1) 0 1).
    unfold open_interval.
    reflexivity.
Qed.

(* Definition for open-closed intervals *)
Definition open_closed_interval (a b : ℝ) : subset ℝ := as_subset ℝ (fun x => a < x <= b).

(* Test 14: Proof that an explicitly defined open-closed interval is an interval *)
Lemma test_explicit_open_closed_interval : is_interval (open_closed_interval 0 1).
Proof.
    apply (Open_Closed (open_closed_interval 0 1) 0 1).
    unfold open_closed_interval.
    reflexivity.
Qed.
