(** * Testcases for changing the global variable [global_search_depth]
Authors: 
    - Lulof Pirée (1363638)
    - Cosmin Manea (small changes)
Creation date: 18 June 2021

Test if importing any of the files in
the directory [set_search_depth] do actually change
the global variable [global_search_depth],
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

Require Import Reals.
Require Import Waterproof.test_auxiliary.
Require Import Waterproof.selected_databases.
Require Import Waterproof.waterprove.waterprove.

Ltac2 Eval print (of_string "Initial search depth is:").
Ltac2 Eval global_search_depth. 
Require Import Waterproof.set_search_depth.To_1.
Ltac2 Eval print (of_string "Current search depth is:").
Ltac2 Eval global_search_depth. 

Open Scope R_scope.

(*
--------------------------------------------------------------------------------
*)(** * Testcases for empty selection
    Only the database [nocore] should be loaded.
*)

(** * Test 1
    Lemma that should be proveable with a search depth of 1.
*)
Lemma search_depth_test_1: True.
    waterprove (Control.goal ()) [] true.
Qed.


(** * Test 2
    Lemma that should NOT be proveable with a search depth of 1.
    (Nor with intuition, which has a larger search depth!)
*)
Lemma search_depth_test_2: forall x: R, (x = 1) -> x = 2 -> (x <> x).
    let result () := waterprove (Control.goal ()) [] true in
    assert_raises_error result.
Abort.

(*
--------------------------------------------------------------------------------
*)(** * Testcases with a search depth of 2
*)

Require Import Waterproof.set_search_depth.To_2.
Ltac2 Eval print (of_string "Current search depth is:").
Ltac2 Eval global_search_depth. 

(** * Test 3
    Same as test 2, but now search depth should be sufficient.
*)
Lemma search_depth_test_3: forall x: R, (x = 1) -> (x = x).
    waterprove (Control.goal ()) [] true.
Qed.