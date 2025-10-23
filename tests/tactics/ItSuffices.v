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
Require Import Waterproof.Util.Assertions.

(* -------------------------------------------------------------------------- *)
(** * Testcases for [It suffices to show that ...]
  Variant without the [by] clause.
*)

Open Scope nat_scope.

(** * Test 1
    Base case: give a statement that indeed suffices.
*)
Lemma test_it_suffices_1: forall x:nat, x>0 /\ x < 2 -> x = S (0).
Proof.
  intros x.
  It suffices to show that x = 1.
  (* Old goal should have been proven by the above,
    now the assumption used remains to be proven.*)
  assert_goal_is constr:(x=1).
Abort.

(** * Test 2
    Error case: give a statement does not suffice to complete the proof.
*)
Lemma test_it_suffices_2: forall A B : Prop , A /\ A -> B.
Proof.
  intros A B.
  (* Clearly this statement isn't helpful in proving the goal! *)
  let result () := By f_increasing it suffices to show that 1 + 1 = 2 in
  assert_raises_error result.
Abort.

Local Parameter f : nat -> nat.
Local Parameter f_increasing : forall m n : nat, m <= n -> f m <= f n.

Lemma test_it_suffices_3: f 1 <= f 2.
  By f_increasing it suffices to show that 1 <= 2.
  assert_goal_is constr:(1 <= 2).
Abort.

(** * Test 2
    Error case: give a statement does not suffice to complete the proof.
*)
Lemma test_it_suffices_2: forall A B : Prop , A /\ A -> B.
Proof.
  intros A B.
  (* Clearly this statement isn't helpful in proving the goal! *)
  Fail By f_increasing it suffices to show that 1 + 1 = 2.
Abort.


(* Test 5: unable to show goal is enough if it does not imply current goal *)
#[local] Parameter A B : Prop.
#[local] Parameter g : A -> B.
Goal B.
  Fail It suffices to show that A.
Abort.

(* Test 6: able to show that goal is enough if it implies current goal. *)
Goal B.
Proof.
  pose g.
  It suffices to show that A.
Abort.

(* Test 7: able to show goal is enough with additional lemma. *)
Goal B.
Proof.
  By g it suffices to show that A.
Abort.

(* Test 8: unable to goal is enough with irrelevant lemma. *)
#[local] Parameter h : A.
Goal B.
Proof.
  Fail By h it suffices to show that A.
Abort.

(* Test 9: this passes, because the type of g is the same as the type of h. *)
Goal B.
  pose g.
  By h it suffices to show that A.
Abort.


(* Test 10: 'Since ...' works. For more tests with 'Since ...', see [tests/.../ItHolds.v] *)
Goal B.
Proof.
  pose g.
  Since A -> B it suffices to show that A.
Abort.

Parameter b : bool.
(* Test 11: "It suffices" works with a boolean statement *)
Goal ((is_true b) -> B) -> B.
Proof.
  intro H.
  Since is_true b -> B it suffices to show that b.
Abort.

(* Test 12: "It suffices" works with a boolean statement *)
Goal ((is_true b) -> B) -> B.
Proof.
  intro H.
  It suffices to show that b.
Abort.

(* Test 13: "It suffices" works with boolean statement and boolean "Since"
  clause *)
Goal ((is_true b) -> B) -> B.
Proof.
  intro H.
  It holds that true.
  Since true it suffices to show that b.
Abort.

(** Test 14: Multiple reasons for it suffices *)

Local Parameter P Q R T : Prop.
Local Parameter HPQ : P -> Q.
Local Parameter HQR : Q -> R.
Local Parameter HRT : R -> T.

Goal T.
Proof.
By HPQ, HQR and HRT it suffices to show that P.
Abort.

(** Test 15: Multiple reasons, but one is also a
  local assumption, using the local assumption. *)

Goal (P -> Q) -> T.
Proof.
  intro H.
  By H, HQR and HRT it suffices to show that P.
Abort.

(** Test 16: Multiple reasons, but one is also a
  local assumption, using the external reason. *)

Goal (P -> Q) -> T.
Proof.
  intro H.
  By HPQ, HQR and HRT it suffices to show that P.
Abort.

(** Test 17: Using an external database as a reason. *)

Local Parameter U V : Prop.
Local Parameter HUV : U -> V.
Local Parameter HVP : V -> P.

Local Create HintDb my_reason.
From Stdlib Require Import String.

Notation "'my' 'reason'" := "my_reason"%string.
Hint Resolve HUV : my_reason.

Notation "'my' 'other' 'reason'" := "my_other_reason"%string.
Hint Resolve HVP : my_other_reason.

Goal V.
Proof.
By my reason it suffices to show that U.
Abort.

(** Test 18: Using two extra databases as a reason, with multiple databases. *)

Goal P.
By my reason and my other reason it suffices to show that U.
Abort.

(** Test 19: Using two extra databases and multiple lemmas as reasons *)

Goal R.
By my reason, HQR, my other reason and HPQ it
  suffices to show that U.
Abort.

(** Test 20: Fails when one of the reasons is not helpful *)

Waterproof Enable Logging.
Waterproof Enable Redirect Errors.

Goal R.
assert_fails_with_string
  (fun () => By my reason, my other reason,
    HPQ, HQR and HRT it suffices to show that U)
  "Could not verify this follows from the provided reasons.".
Abort.
