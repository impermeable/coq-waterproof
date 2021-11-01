(** * Testcases for changing the global variable [global_enable_intuition]
Authors: 
    - Lulof Pirée (1363638)
Creation date: 21 June 2021

Test if importing any of the files in
the directory [set_intuition] do actually change
the global variable [global_enable_intuition],
AND change the behaviour of [waterprove].

--------------------------------------------------------------------------------

This file is part of Waterproof-lib.

Waterproof-lib is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

Waterproof-lib is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with Waterproof-lib.  If not, see <https://www.gnu.org/licenses/>.
*)

From Ltac2 Require Import Ltac2.
From Ltac2 Require Option.
From Ltac2 Require Import Message.

Require Import Waterproof.test_auxiliary.
Require Import Waterproof.selected_databases.
Require Import Waterproof.waterprove.waterprove.


(** * Test 1
    Without intuition, this call to [waterprove] should fail.
*)
Require Import Waterproof.set_intuition.Disabled.
Lemma test_1: forall A B: Prop, A /\ B -> B /\ A.
    let result () := waterprove (Control.goal ()) [] false in
    assert_raises_error result.
Abort.

(** * Test 2
    With intuition, [waterprove] should be able to solve it.
*)
Require Import Waterproof.set_intuition.Enabled.
Lemma test_2: forall A B: Prop, A /\ B -> B /\ A.
    intros.
    waterprove (Control.goal ()) [] false.
Qed.