Require Import Ltac2.Ltac2.
Require Import Ltac2.Message.

Require Import Coq.Reals.Reals.

Require Import Waterproof.Waterproof.
Require Import Waterproof.Automation.
Require Import Waterproof.Notations.
Require Import Waterproof.Tactics.
Require Import Waterproof.Util.Assertions.

Waterproof Enable Automation RealsAndIntegers.

Open Scope R_scope.

(** Test 0: This tests to see if x <= 0 or 0 < x*)
Goal forall x : R, exists n : nat, INR(n) > x.
    intro x.
    Either (x <= 0) or (0 < x).
    - Case (x <= 0).
      Fail Case (x <= 0).
      admit.
    - Fail Case (x <= 0).
      Case (0 < x).
Abort.

(** Test 2: This tests to see if x > 0 or x <= 0 (test commutativity, flipping one term) *)
Goal forall x : R, exists n : nat, INR(n) > x.
    intro x.
    Either  (x > 0) or (x <= 0).
    - Case (x > 0).
      Fail Case (x < 0).
      admit.
    - Fail Case (x > 0).
      Case (x <= 0).
Abort.


(** Test 3: This tests to see if x > 1 or x <= 1 *)
Goal forall x : R, exists n : nat, INR(n) > x.
    intro x.
    Either (x <= 1) or (1 < x).
    - Case (x <= 1).
      Fail Case (x <= 0).
      admit.
    - Fail Case (x <= 0).
      Case (1 < x).
Abort.

(** Test 4: This tests to see what error is thrown if we try a nonsense case analysis. *)
Goal forall x : R, exists n : nat, INR(n) > x.
    intro x.
    Fail Either (x <= 1) or (x > 2).
Abort.

Local Lemma sumbool_comm (A B : Prop) : {A} + {B} -> {B} + {A}.
Proof.
  intro H.
  induction H.
  right; exact a.
  left; exact b.
Qed.

(** Test 5: This tests whether given x >= 0, either x > 0 or x = 0. 
            Also tests whether the hypothesis name from the tactic can be chosen flexibly. *)
Goal forall x : R, x >= 0 -> exists n : nat, INR(n) > x.
  intros x h.
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
      admit.
    - Case (x > 0).
Abort.

(** Test 6: This tests whether given x >= 0, either x = 0 or x > 0 (commutativity). *)
Goal forall x : R, x >= 0 -> exists n : nat, INR(n) > x.
  intros x H.
Abort.
(*     Either (x = 0) or (x > 0).
    - Case (x = 0).
      admit.
    - Case (x > 0).
Abort. *)

(** Test 7: This tests to see if 0 < x, x = 0 or 0 < x. *)
Goal forall x : R, exists n : nat, INR(n) > x.
    intro x.
    Either (x < 0), (x = 0) or (0 < x).
    - Case (x < 0).
      admit.
    - Case (x = 0).
      admit.
    - Case (0 < x).
Abort.

(** Test 8: This tests to see if x = 0, x < 0 or 0 < x (commutativity, flipped sign). *)
Goal forall x : R, exists n : nat, INR(n) > x.
    intro x.
    Either (x = 0), (x < 0) or (0 < x).
    - Case (x = 0).
      admit.
    - Case (x < 0).
      admit.
    - Case (0 < x).
Abort.

(** Test 9: This tests to see if 0 < x, x = 0 or x > 0, (flipped sign). *)
Goal forall x : R, exists n : nat, INR(n) > x.
    intro x.
    (*assert (sumtriad (x < 0) (x = 0) (x > 0)).
    unfold Rgt. *)
    Either (x < 0), (x = 0) or (x > 0).
    - Case (x < 0).
      admit.
    - Case (x = 0).
      admit.
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
  left.
  assumption.
* Case (~A).
  right.
  assumption.
Abort.

Goal forall P Q : Prop, P \/ Q -> {P} + {Q}.
Proof.
intros P Q H.
Either (P) or (Q).
* Case (P).
  left.
  assumption.
* Case (Q).
  right.
  assumption.
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
