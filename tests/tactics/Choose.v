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

(** Test 0: This should choose m equal to n *)
Goal forall n : nat, exists m : nat, n = m.
Proof.
  intros.
  Choose m := n.
  reflexivity.
Qed.

(** Test 1: This should choose m equal n implicitly *)
Goal forall n : nat, exists m : nat, n = m.
    intro n.
    Choose (n).
    reflexivity.
Qed.


(** Test 2: This should choose m equal to 1 *)
Goal exists m : nat, m = 1.
    Choose m := 1.
    reflexivity.
Qed.


(** Test 3: This should raise an error, as the goal is not an exists goal *)
Goal forall n : nat, ( ( (n = n) \/ (n + 1 = n + 1) ) -> (n + 1 = n + 1)).
    intro n.
    Fail Choose (n).
Abort.


(** Test 4: This should also raise an error, as the goal is not an exists goal *)
Goal forall n : nat, ( ( (n = n) \/ (n + 1 = n + 1) ) -> (n + 1 = n + 1)).
    intro n.
    Fail Choose m := n.
Abort.

(** Test 5: Choose a blank *)
Goal exists n : nat, n + 1 = n + 1.
    Choose n := (_).
Abort.

(** Test 6: Choose a named evar *)
Goal exists n : nat, n + 1 = n + 1.
    Choose n := (?[m]).
Abort.

(** Test 7: Choose a blank check tha blank was renamed *)
Goal exists n : nat, n + 1 = n + 1.
    Choose n := (_).
    assert (?n = 0).
Abort.

(** Test 8: Choose a more complicated blank and check that renaming took place, 
    by reformulating the goal in terms of the new named evars. *)
Goal exists n : nat, n + 1 = n + 1.
    Choose n := (_ + _ + _).
    change (?n + ?n0 + ?n1 + 1 = ?n + ?n0 + ?n1 + 1).
Abort.
