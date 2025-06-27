Require Import Ltac2.Ltac2.
Require Import Ltac2.Message.

From Stdlib Require Import Reals.Reals.

Require Import Waterproof.Waterproof.
Require Import Waterproof.Automation.
Require Import Waterproof.Notations.
Require Import Waterproof.Tactics.
Require Import Waterproof.Util.Assertions.

Waterproof Enable Automation RealsAndIntegers.

Open Scope R_scope.

(** Test 0: This tests to see if x <= 0 or 0 < x*)
Goal forall x : R, exists n : nat, INR(n) > x.
    ltac2: intro x.
    Either (x <= 0) or (0 < x).
    - Case (x <= 0).
      Fail Case (x <= 0).
      ltac2: admit.
    - Fail Case (x <= 0).
      Case (0 < x).
Abort.

(** Test 2: This tests to see if x > 0 or x <= 0 (test commutativity, flipping one term) *)
Goal forall x : R, exists n : nat, INR(n) > x.
    ltac2: intro x.
    Either  (x > 0) or (x <= 0).
    - Case (x > 0).
      Fail Case (x < 0).
      ltac2: admit.
    - Fail Case (x > 0).
      Case (x <= 0).
Abort.


(** Test 3: This tests to see if x > 1 or x <= 1 *)
Goal forall x : R, exists n : nat, INR(n) > x.
    ltac2: intro x.
    Either (x <= 1) or (1 < x).
    - Case (x <= 1).
      Fail Case (x <= 0).
      ltac2: admit.
    - Fail Case (x <= 0).
      Case (1 < x).
Abort.

(** Test 4: This tests to see what error is thrown if we try a nonsense case analysis. *)
Goal forall x : R, exists n : nat, INR(n) > x.
    ltac2: intro x.
    Fail Either (x <= 1) or (x > 2).
Abort.

Local Lemma sumbool_comm (A B : Prop) : {A} + {B} -> {B} + {A}.
Proof.
  ltac2: intro H.
  ltac2: induction H.
  ltac2: (right; exact a).
  ltac2: (left; exact b).
Qed.

(** Test 5: This tests whether given x >= 0, either x > 0 or x = 0.
            Also tests whether the hypothesis name from the tactic can be chosen flexibly. *)
Goal forall x : R, x >= 0 -> exists n : nat, INR(n) > x.
  ltac2: intros x h.
  (* assert ({0 = x} + {0 < x}).
  apply sumbool_comm.
  apply Rle_lt_or_eq_dec.
  apply Rge_le.
  Locate Rle_lt_or_eq_dec.
  apply .

  auto with wp_decidability_reals. *)
  (* apply sumbool_comm.
  apply Rle_lt_or_eq_dec.
  auto with wp_reals. *)
  (*assert ({0 < x} + {0 = x}). *)
  (* auto with wp_decidability_reals wp_reals. *)
  Either (0 = x) or (x > 0).
    - Case (0 = x).
      ltac2: admit.
    - Case (x > 0).
Abort.

(** Test 6: This tests whether given x >= 0, either x = 0 or x > 0 (commutativity). *)
Goal forall x : R, x >= 0 -> exists n : nat, INR(n) > x.
  ltac2: intros x H.
Abort.
(*     Either (x = 0) or (x > 0).
    - Case (x = 0).
      admit.
    - Case (x > 0).
Abort. *)

(** Test 7: This tests to see if 0 < x, x = 0 or 0 < x. *)
Goal forall x : R, exists n : nat, INR(n) > x.
    ltac2: intro x.
    Either (x < 0), (x = 0) or (0 < x).
    - Case (x < 0).
      ltac2: admit.
    - Case (x = 0).
      ltac2: admit.
    - Case (0 < x).
Abort.

(** Test 8: This tests to see if x = 0, x < 0 or 0 < x (commutativity, flipped sign). *)
Goal forall x : R, exists n : nat, INR(n) > x.
    ltac2: intro x.
    Either (x = 0), (x < 0) or (0 < x).
    - Case (x = 0).
      ltac2: admit.
    - Case (x < 0).
      ltac2: admit.
    - Case (0 < x).
Abort.

(** Test 9: This tests to see if 0 < x, x = 0 or x > 0, (flipped sign). *)
Goal forall x : R, exists n : nat, INR(n) > x.
    ltac2: intro x.
    (*assert (sumtriad (x < 0) (x = 0) (x > 0)).
    unfold Rgt. *)
    Either (x < 0), (x = 0) or (x > 0).
    - Case (x < 0).
      ltac2: admit.
    - Case (x = 0).
      ltac2: admit.
    - Case (0 < x). (* Note that this also works although the literal case is x > 0 =) *)
Abort.

Waterproof Disable Automation RealsAndIntegers.

(** Test 10: Without loading classical decidability, this shouldn't work *)
Local Parameter A : Prop.
Goal False.
Fail Either (A) or (~A).
Abort.

(** Test 11: Now load classical informative decidability and try again *)

Waterproof Enable Automation RealsAndIntegers.

Goal False.
  Either (A) or (~A).
Abort.

Waterproof Disable Automation RealsAndIntegers.

Waterproof Enable Automation ClassicalEpsilon.

Goal {A} + {~A}.
Either (A) or (~A).
* Case (A).
  ltac2: left.
  ltac2: assumption.
* Case (~A).
  ltac2: right.
  ltac2: assumption.
Abort.

Goal forall P Q : Prop, P \/ Q -> {P} + {Q}.
Proof.
ltac2: intros P Q H.
Either (P) or (Q).
* Case (P).
  ltac2: left.
  ltac2: assumption.
* Case (Q).
  ltac2: right.
  ltac2: assumption.
Qed.

Waterproof Disable Automation ClassicalEpsilon.

Close Scope R_scope.

Section test_differences_sort_of_goal.

Variable P : Prop.
Hypothesis P_dec : P \/ ~P.

(** Test 12: without loading additional databases, we should not be able to get informative excluded middle from decidability *)

Goal {P} + {~P}.
Proof.
Fail Either (P) or (~P).
Abort.

End test_differences_sort_of_goal.

(** Test 13: Check whether we can handle boolean statements *)
From Stdlib Require Import Bool.
Goal forall b : bool, is_true(eqb b true) \/ is_true(eqb b false) -> True.
Proof.
  ltac2: intro b.
  Assume that (is_true(eqb b true) \/ is_true(eqb b false)).
  Either (eqb b true) or (eqb b false).
  - Case (eqb b true).
    ltac2: exact I.
  - Case (eqb b false).
    ltac2: exact I.
Qed.

(** Test 14: Check whether we can handle boolean statements in the 3-or case *)
Goal forall b : bool, is_true (eqb b true) \/ is_true (eqb b false) \/ is_true (eqb b false) -> True.
  ltac2: intro b.
  Assume that (is_true (eqb b true) \/ is_true (eqb b false) \/ is_true (eqb b false)).
  Either (eqb b true), (eqb b false) or (eqb b false).
  - Case (eqb b true).
    ltac2: exact I.
  - Case (eqb b false).
    ltac2: exact I.
  - Case (eqb b false).
    ltac2: exact I.
Qed.

Waterproof Enable Automation RealsAndIntegers.
Open Scope nat_scope.
(** Test 15: Test for the right notation in the goal*)
Goal forall x : nat, x = x.
Proof.
  ltac2: intro x.
  Either (x < 0) or (x ≥ 0).
  ltac2: let s := Message.to_string (Message.of_constr (Control.goal ())) in
  assert_string_equal s
(String.concat "" ["(Add the following line to the proof:
";" ";"
 - Case (x < 0).)"]).
Abort.

Close Scope nat_scope.

Waterproof Disable Automation RealsAndIntegers.
