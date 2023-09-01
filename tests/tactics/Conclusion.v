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

Require Import Coq.Reals.Reals.
Require Import micromega.Lra.

Require Import Waterproof.Waterproof.
Require Import Waterproof.Automation.
Require Import Waterproof.Notations.
Require Import Waterproof.Tactics.
Require Import Waterproof.Util.Assertions.

Waterproof Enable Automation RealsAndIntegers.

(* lra only works in the [R_scope] *)
Open Scope R_scope.
Lemma zero_lt_one: 0 < 1.
Proof.
    ltac1:(lra).
Qed.

(* -------------------------------------------------------------------------- *)
(** * Testcases for [We conclude that ... ] *)

(** * Test 1
    Base case: should easily be possible to finish the goal.
*)
Lemma test_we_conclude_1: True.
Proof.
    We conclude that True.
Qed.

(** * Test 2
    Error case: wrong goal provided.
*)
Lemma test_we_conclude_2: True.
Proof.
    Fail We conclude that False.
Abort.

(** * Test 3
    Warning case: provided goal is equivalent, 
        but uses an alternative notation.
*)
Lemma test_we_conclude_3: 2 = 2.
Proof.
    print (of_string "Should raise warning:").
    We conclude that (1+1 = 2).
Qed.

(** * Test 4
    Base case, like test 1 but more complex goal.
*)
Lemma test_we_conclude_4: forall A: Prop, (A \/ ~A  -> True).
Proof.
    intros A h.
    We conclude that (True).
Qed.

(** * Test 5
    Removed test case because it takes too long.

    Error case: Waterprove cannot find proof
    (because the statement is false!).

Lemma test_we_conclude_5: 0 = 1.
Proof.
    let result () := We conclude that (0 = 1) in
    assert_raises_error result.
Abort. *)

(** * Test 6
    Alternative [It follows that ...] notation.
*)
Lemma test_we_conclude_6: True.
Proof.
    It follows that True.
Qed.

(* -------------------------------------------------------------------------- *)
(** * Testcases for [By ... we conclude that ... ] *)

(** * Test 1
    Base case: should easily be possible to finish the goal,
    even with the provided lemma.

    NOTE: this test would also pass if we just
    write 
    [We conclude that (2 = 1).]
    Applarently, waterprove is powerful enough to apply symmetry to hypotheses.
*)
Lemma test_by_we_conclude_1: (1 = 2) -> (2 = 1).
Proof.
    intros h.
    apply eq_sym in h. (* Rewrite h as (2 = 1) using symmetry of "="*)
    By h we conclude that (2 = 1).
Qed.


(** * Test 3
    Warning case: provided goal is equivalent, 
        but uses an alternative notation.
*)
Lemma test_by_we_conclude_3: 2 = 1 + 1.
Proof.
    print (of_string "Should raise warning:").
    We conclude that (2 = 2).
Qed.

(** * Test 5
    Shows that [waterprove]
    can solve [(1 < 2)]
    without explcitly being given 
    the lemma that states [0 < 1].
*)
Lemma test_by_we_conclude_5: 1 < 2.
Proof.
    assert (useless: 1 = 1).
    reflexivity.
    Fail By test_by_we_conclude_1 we conclude that (1 < 2).
Abort.

(** Additional tests 'By ...' clause.  *)
(* Test 6: unable to show goal without means required for proof. *)
Variable A B : Prop.
Variable f : A -> B.
Goal A -> B.
  intro H.
  Fail We conclude that B.
Abort.

(* Test 7: able to show that goal with means required for proof. *)
Goal A -> B.
Proof.
  intro H.
  pose f.
  We conclude that B.
Qed.

(* Test 8: able to show goal with additional lemma. *)
Goal A -> B.
Proof.
  intro H.
  By f we conclude that B.
Qed.

(* Test 9: unable to show goal with irrelevant lemma. *)
Variable g : B -> A.
Goal B.
Proof.
  Fail By g we conclude that B.
Abort.

(* Test 10: unable to show goal with superfluous lemma. *)
Goal A -> B.
  intro H.
  pose f.
  Fail By g we conclude that B.
Abort.


(* Test 11: 'Since ...' works. 
  For more tests with 'Since ...', see [tests/.../ItHolds.v] *)
Goal A -> B.
Proof.
  intro H.
  pose f.
  Since (A -> B) we conclude that B.
Abort.


(** * Example for the SUM.
    Somewhat more realistic context.
*)

Open Scope nat_scope.
Inductive even : nat -> Prop :=
    even0 : even 0
  | evenS : forall x:nat, even x -> even (S (S x)).

Lemma sum_example_by_we_conclude: forall x:nat, x = 2 -> even x.
Proof.
    intros x h.
    rewrite h. (* Change the goal to "even 2"*)
    apply evenS. (* Change the goal to "even 0"*)
    By even0 we conclude that (even 0).
Qed.

Open Scope R_scope.

(** * Test 4
Should accept chain of inequalities as being 'equal' to the goal.
*)
Goal (3 < 5).
We conclude that (& 3 < 4 < 5).
Qed.

Goal (3 = 3).
We conclude that (& 3 = 3 = 3).
Qed.


Goal forall eps : R, eps > 0 -> (Rmin (eps / 2) 1 <= eps).
intro eps.
intro eps_gt_0.
assert (& Rmin (eps/2) 1 <= eps/2 <= eps).
cbn; repeat split.
auto with wp_core wp_reals.
auto with wp_reals.
auto with wp_core wp_reals.
Qed.

Close Scope R_scope.

(** 'We conclude that' should accept (in nat_scope) (& 3 < 4 < 5) for (3<5).*)
Goal (3 < 5).
We conclude that (& 3 < 4 < 5).
Qed.

(** 'We conclude that' should accept (in nat_scope) (& 3 < 4 <= 5) for (3<5).*)
Goal (3 < 5).
We conclude that (& 3 < 4 <= 5).
Qed.

(** 'We conclude that' should accept (in nat_scope) (& 3 <4 < 5) for (3<=5).*)
Goal (3 <= 5).
We conclude that (& 3 < 4 < 5).
Qed.


(** * Test 6
  Test whether wrapped goals requiring users to write out what they need to show
  can be solved immediately. It is irritating to have to write something like:
    'We need to show that (a < b).'
    'We conclude that (a < b).'
*)

Goal (StateGoal.Wrapper (0 = 0)).
Proof.
  We conclude that (0 = 0).
Qed.

(** * Test 7
  Test whether the tactic throws an error for other wrappers.
*)
Goal (Case.Wrapper (0 = 1) (0 = 0)).
Proof.
  Fail We conclude that (0 = 0).
Abort.
