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

Waterproof Enable Redirect Feedback.
Waterproof Enable Redirect Errors.

Definition foo : nat := 0.

(* Tests general unfolding: *)

(* Test 1: unfold term in goal, and throws an error suggesting
  to remove the line after use. *)
Goal foo = 1.
Proof.
  assert_feedback_with_strings
  (fun () =>
  assert_fails_with_string
  (fun () => Expand the definition of foo)
"Remove this line in the final version of your proof.")
  Info
["Expanded definition in statements where applicable.";
"Hint, replace with: We need to show that (0 = 1)."].
Abort.

(* Test 2: unfold term in hypothese and goal, and throws an error suggesting
    to remove the line after use. *)
Goal (foo = 0) -> (foo = 2) -> (foo = 1).
Proof.
  intros.
  assert_feedback_with_strings
  (fun () =>
  assert_fails_with_string
  (fun () => Expand the definition of foo)
"Remove this line in the final version of your proof.")
  Info
["Expanded definition in statements where applicable.";
"Hint, insert: We need to show that (0 = 1).";
"Hint, insert: It holds that (0 = 0).";
"Hint, insert: It holds that (0 = 2)."].
Abort.


(* Tests framework expand the definition. *)
Local Ltac2 unfold_foo (statement : constr) := eval unfold foo in $statement.
Ltac2 Notation "Expand" "the" "definition" "of" "foo2" x(opt(seq("in", constr))) :=
  wp_unfold unfold_foo (Some "foo2") true true x.

(* Test 6: unfold term in hypotheses and goal and throws an error suggesting
    to remove line after use. *)
Goal (foo = 0) -> (foo = 2) -> (foo = 1).
Proof.
  intros.
  assert_feedback_with_strings
  (fun () =>
  assert_fails_with_string
  (fun () => Expand the definition of foo)
"Remove this line in the final version of your proof.")
  Info
["Expanded definition in statements where applicable.";
"Hint, insert: We need to show that (0 = 1).";
"Hint, insert: It holds that (0 = 0).";
"Hint, insert: It holds that (0 = 2)."].
Abort.

(* Test 7: fails to unfold term in statment without term. *)
Goal False.
Proof.
  assert_feedback_with_strings
  (fun () =>
  assert_fails_with_string
  (fun () => Expand the definition of foo)
"Remove this line in the final version of your proof.")
  Info
["Definition does not appear in any statement."].
Abort.

Local Parameter P Q R : Prop.
Local Parameter HPQ : P <-> Q.
Local Hint Resolve HPQ : core.
Local Hint Resolve <- HPQ : core.

(* Test 8: Use the [apply_in_constr] tactic for an alternative characterization *)
Ltac2 Notation "Expand" "the" "definition" "of" "foo3" x(opt(seq("in", constr))) :=
  wp_unfold (apply_in_constr constr:(HPQ)) (Some "foo3") true false x.
Goal Q -> R -> Q.
Proof.
  intros.
  assert_feedback_with_strings
  (fun () =>
  assert_fails_with_string
  (fun () => Expand the definition of foo3)
"Remove this line in the final version of your proof.")
  Info
["Applied alternative characterizations in statements where applicable.";
"Hint, insert: It suffices to show that P.";
"Hint, insert: It holds that P."].
It suffices to show that P.
It holds that P.
Abort.

From Stdlib Require Import Reals.Reals.
Require Import Waterproof.Notations.Common.
Require Import Waterproof.Notations.Reals.
Require Import Waterproof.Notations.Sets.
Require Import Waterproof.Libs.Analysis.SupAndInf.


Open Scope R_scope.

Local Parameter A : subset R.

(* Test 9, test for infimum, as it is important that it works in practice. *)
Goal 4 is the infimum of A -> 3 is the infimum of A.
Proof.
intro H.
assert_feedback_with_strings
  (fun () =>
  assert_fails_with_string
  (fun () => Expand the definition of infimum)
"Remove this line in the final version of your proof.")
  Info
["Expanded definition in statements where applicable.";
"Hint, insert: We need to show that (3 is a _lower bound_ for A
                      ∧ (∀ l ∈ ℝ, l is a _lower bound_ for A ⇨ l ≤ 3)).";
"Hint, insert: It holds that (4 is a _lower bound_ for A
               ∧ (∀ l ∈ ℝ, l is a _lower bound_ for A ⇨ l ≤ 4)).";
"Applied alternative characterizations in statements where applicable.";
"Hint, insert: It suffices to show that (3 is a _lower bound_ for A
                          ∧ (∀ ε > 0, ∃ a ∈ A, a < 3 + ε)).";
"Hint, insert: It holds that (4 is a _lower bound_ for A ∧ (∀ ε > 0, ∃ a ∈ A, a < 4 + ε))."].
Abort.

(* Test 10, test for supremum, as it is important that it works in practice. *)
Goal 4 is the supremum of A -> 3 is the supremum of A.
Proof.
intro H.
assert_feedback_with_strings
  (fun () =>
  assert_fails_with_string
  (fun () => Expand the definition of supremum)
"Remove this line in the final version of your proof.")
  Info
["Expanded definition in statements where applicable.";
"Hint, insert: We need to show that (3 is an _upper bound_ for A
                      ∧ (∀ L ∈ ℝ, L is an _upper bound_ for A ⇨ 3 ≤ L)).";
"Hint, insert: It holds that (4 is an _upper bound_ for A
               ∧ (∀ L ∈ ℝ, L is an _upper bound_ for A ⇨ 4 ≤ L)).";
"Applied alternative characterizations in statements where applicable.";
"Hint, insert: It suffices to show that (3 is an _upper bound_ for A
                          ∧ (∀ ε > 0, ∃ a ∈ A, 3 - ε < a)).";
"Hint, insert: It holds that (4 is an _upper bound_ for A ∧ (∀ ε > 0, ∃ a ∈ A, 4 - ε < a))."].
Abort.

Close Scope R_scope.
Open Scope nat_scope.

(** Check unfolding method that does not throw an error.
  Meant for internal use by custom Waterproof editor. *)

(** Non-framework version. *)

(* Test 11: unfold term in hypotheses and goal without throwing an error. *)
Goal (foo = 0) -> (foo = 2) -> (foo = 1).
Proof.
  intros.
  _internal_ Expand the definition of foo.
Abort.

(* Test 12: unfold fails to unfold term if no statement with term. *)
Goal False.
Proof.
  _internal_ Expand the definition of foo.
Abort.

(** Framework version:  *)

Ltac2 Notation "_internal_" "Expand" "the" "definition" "of" "foo2" :=
  wp_unfold unfold_foo (Some "foo2") false true None.

(* Test 13: unfold term in hypotheses and goals. *)
Goal (foo = 0) -> (foo = 2) -> (foo = 1).
Proof.
  intros.
  _internal_ Expand the definition of foo2.
Abort.

(* Test 13: fails to unfold term if no statements with term. *)
Goal False.
Proof.
   _internal_ Expand the definition of foo2.
Abort.
