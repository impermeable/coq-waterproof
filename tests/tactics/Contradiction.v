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
Require Import Waterproof.Notations.
Require Import Waterproof.Tactics.
Require Import Waterproof.Util.Assertions.

(** Test 0: this should start with the proof by contradicition. *)
Goal forall n : nat, n = n.
Proof.
    We argue by contradiction.
    Assume that (¬ (for all n : ℕ, n = n)).
Abort.


(** Test 1: this should work and completely finish the proof. *)
Goal forall n : nat, n = n.
Proof.
    intro n.
    We argue by contradiction.
    Assume that (n ≠ n).
    Contradiction.
Qed.

(** Test 2: this should work and completely finish the proof. *)
Goal forall n : nat, n = n.
Proof.
    intro n.
    We argue by contradiction.
    Assume that (n ≠ n).
    It holds that (n = n). ↯.
Qed.

(** Test 3: wrong assumption specified for wrapper. *)
Goal forall n : nat, n = n.
Proof.
    We argue by contradiction.
    Fail Assume that (¬ (for all n : nat, n ≠ n)).
Abort.


(** Test 4: fails if previous statement is not a contraditcion 
    to some earlier statement. *)
Variable P Q A : Prop.
Goal P -> Q.
    intro H.
    Fail Contradiction.
Abort.

(** Test 5: fails to negate sets and types. *)
Goal nat -> Q.
    intro x.
    Fail Contradiction.
Abort.

(* Test 6: Fail to circumvent shielding by attempting to 
    ask automation to find proof of ~~goal. *)
Goal P -> (P -> A) -> (A -> Q) -> P /\ Q.
Proof.
    intros Hp H1 H2.
    Fail We conclude that (P /\ Q).
    We argue by contradiction.
    Assume that (~ (P /\ Q)).
    Fail Contradiction.
Abort.

(** Test 7: Fails if no hypotheses.  *)
Goal P.
Proof.
    Fail Contradiction.
Abort.
