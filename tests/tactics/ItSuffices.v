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
  It suffices to show that (x = 1).
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
  let result () := By (f_increasing) it suffices to show that (1 + 1 = 2) in
  assert_raises_error result.
Abort.

Local Parameter f : nat -> nat.
Local Parameter f_increasing : forall m n : nat, m <= n -> f m <= f n.

Lemma test_it_suffices_3: f 1 <= f 2.
  By f_increasing it suffices to show that (1 <= 2).
  assert_goal_is constr:(1 <= 2).
Abort.

(** * Test 2
    Error case: give a statement does not suffice to complete the proof.
*)
Lemma test_it_suffices_2: forall A B : Prop , A /\ A -> B.
Proof.
  intros A B.
  (* Clearly this statement isn't helpful in proving the goal! *)
  Fail By (f_increasing) it suffices to show that (1 + 1 = 2).
Abort.


(* Test 5: unable to show goal is enough if it does not imply current goal *)
Variable A B : Prop.
Variable g : A -> B.
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
Variable h : A.
Goal B.
Proof.
  Fail By h it suffices to show that A.
Abort.

(* Test 9: unable to show goal if lemma is superfluous. *)
Goal B.
  pose g.
  Fail By h it suffices to show that A.
Abort.


(* Test 10: 'Since ...' works. For more tests with 'Since ...', see [tests/.../ItHolds.v] *)
Goal B.
Proof.
  pose g.
  Since (A -> B) it suffices to show that A.
Abort.