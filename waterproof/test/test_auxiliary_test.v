(** * Testcases for [test_auxiliary.v]
Authors: 
    - Lulof Pirée (1363638)
Creation date: 20 May 2021

Testcases for the functions used to build testcases.
It is assumes that [assert_raises_error] is correct,
and using this assumption it is tested that the other
functions in [test_auxiliary.v] are correct.

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

Load test_auxiliary.

(*
--------------------------------------------------------------------------------
*) (** *    Testcases for [assert_list_equal]
*)
Ltac2 Eval assert_list_equal (constr:(1)::constr:(2)::constr:(3)::[])
                             (constr:(1)::constr:(2)::constr:(3)::[]).

Ltac2 Eval assert_list_equal [] [].                             

Ltac2 Eval assert_raises_error (fun () =>
assert_list_equal (constr:(1)::constr:(3)::[]) (constr:(2)::constr:(3)::[]) ).

(*
--------------------------------------------------------------------------------
*)(** * Testcase for [assert_hyp_exists]
*)
Goal forall n, n = 1.
    intros n.
    assert_hyp_exists @n.
    assert_raises_error (fun () => assert_hyp_exists @x).
Abort.

(*
--------------------------------------------------------------------------------
*)(** * Testcase for [assert_hyp_has_type]
*)
Goal forall n: nat, n = 1 -> n = 1.
    intros n h.
    assert_hyp_has_type @n constr:(nat).
    assert_hyp_has_type @h constr:(n = 1).

    (* Wrong ident *)
    assert_raises_error (fun () => assert_hyp_has_type @m constr:(nat)).
    (* Wrong type *)
    assert_raises_error (fun () => assert_hyp_has_type @n constr:(bool)).
Abort.


(*
--------------------------------------------------------------------------------
*) (** *    Testcases for [assert_constr_is_true]
*)
Ltac2 Eval assert_constr_is_true constr:(true).
Ltac2 Eval assert_raises_error 
    (fun () => assert_constr_is_true constr:(false)).
    Ltac2 Eval assert_raises_error 
    (fun () => assert_constr_is_true constr:(1)).

(*
--------------------------------------------------------------------------------
*) (** *    Testcases for [assert_is_true] and [assert_is_false].
*)
Ltac2 Eval assert_is_true (true).
Ltac2 Eval assert_raises_error 
    (fun () => assert_is_true false).

Ltac2 Eval assert_is_false (false).
Ltac2 Eval assert_raises_error 
    (fun () => assert_is_false true).

(*
--------------------------------------------------------------------------------
*) (** * Testcases for [assert_goal_is]
*)

(** * Test 1
    Target does equal goal, no error should be raised.
*)
Lemma test_assert_goal_1: forall x:nat, x >= 0.
Proof.
    let t := constr:(forall x:nat, x >= 0) in
    assert_goal_is t.
Abort.

(** * Test 2
    Target does not equal goal, an error should be raised.
*)
Lemma test_assert_goal_2: forall x:nat, x >= 0.
Proof.
    let t := constr:(forall x:nat, x < 0) in
    let result () := assert_goal_is t in
    assert_raises_error result.
Abort.

(*
--------------------------------------------------------------------------------
*) (** * Testcases for [assert_constr_equal]
*)

Ltac2 Eval assert_constr_equal constr:(1 < 2) constr:(1 < 2).
Ltac2 Eval let result () := assert_constr_equal constr:(1 < 2) 
                                                constr:(1 > 2) in
    assert_raises_error result.