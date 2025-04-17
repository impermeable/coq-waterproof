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

(* ---------------------------------------------------------------------------*)
(**
    * Testcases for [such that].
    Subset of tests for [Assume],
    as they do exactly the same anyway.
*)

(** * Test 1
    Base case: only nested conjunctions in premise.
    Do not break down as deeply as possible,
    as the input list still contains conjunctions!
*)
Goal forall A B C: Prop, (A /\ B) /\ (B /\ C) -> (A /\ C).
    intros A B C.
    Fail such that (A /\ B) and (B /\ C).
    (*assert_hyp_has_type @ab constr:(A /\ B).
    assert_hyp_has_type @bc constr:(B /\ C).*)
Abort.

(** * Test 2
    Base case: only nested conjunctions in premise.
    Do break some parts of the hypothesis to atomic expression,
    leave conjunction in others.
*)
Goal forall A B C: Prop, (A /\ B) /\ (B /\ C) -> (A /\ C).
    intros A B C.
    Fail such that A and B and (B /\ C).
    (*assert_hyp_has_type @a constr:(A).
    assert_hyp_has_type @b constr:(B).
    assert_hyp_has_type @bc constr:(B /\ C).*)
Abort.

Goal forall n, n = 1 -> n <> 2.
    intros n.
    such that (n = 1).
Abort.

Goal forall x:nat, (x > 1) -> (x > 0).
Proof.
    Take x : nat; such that (x > 1) as (i).
    assert_hyp_has_type @x constr:(nat).
    assert_hyp_has_type @i constr:(x > 1).
Abort.