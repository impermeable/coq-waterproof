(** * Testcases for [rewrite_inequalities.v]
Authors: 
    - Lulof Pirée (1363638)
Creation date: 11 June 2021

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


Require Import Waterproof.message.

Require Import Waterproof.init_automation_global_variables.
Require Import Waterproof.set_intuition.Disabled.
Require Import Waterproof.set_search_depth.To_5.
Require Import Waterproof.load_database.All.
Require Import Waterproof.test_auxiliary.
Require Import Waterproof.load_database.DisableWildcard.
Load rewrite_inequalities.

(*
--------------------------------------------------------------------------------
*) (** * Testcases for [string_to_ineq]
*)

Ltac2 Eval
    match string_to_ineq "<" with
    | Less => ()
    | _ => fail_test "Wrong output given"
    end.

Ltac2 Eval
    match string_to_ineq "<=" with
    | LessEq => ()
    | _ => fail_test "Wrong output given"
    end.

Ltac2 Eval
    match string_to_ineq "≤" with
    | LessEq => ()
    | _ => fail_test "Wrong output given"
    end.

Ltac2 Eval
    match string_to_ineq ">" with
    | Greater => "ok"
    | _ => fail_test "Wrong output given"
    end.

Ltac2 Eval
    match string_to_ineq ">=" with
    | GreaterEq => "ok"
    | _ => fail_test "Wrong output given"
    end.

Ltac2 Eval
    match string_to_ineq "≥" with
    | GreaterEq => "ok"
    | _ => fail_test "Wrong output given"
    end.

Ltac2 Eval
    match string_to_ineq "=" with
    | Eq => "ok"
    | _ => fail_test "Wrong output given"
    end.

Ltac2 Eval 
    let result () :=
        match string_to_ineq "=" with
        | Greater => ()
        | _ => fail_test "Wrong output given"
        end
    in
    assert_raises_error result; "ok".

(*
--------------------------------------------------------------------------------
*) (** * Testcases for [convert_to_chain]
*)

(** * Test 1
    Expected output:
    [
        Chain list = [
            ChainLink ((constr:(A), Less, constr:(B)));
            ChainLink ((constr:(B), LessEq, constr:(C)));
            ChainEnd
            ]
    ]

    TEST NOT AUTOMATED - DO CHECK THE OUTPUT MANUALLY
    (automatic tests are very troublesome 
     with custom types in Ltac2).
    *)
Lemma test_convert_to_chain_1: forall A B C: Prop, 1=1.
    intros A B C.
    (* To see the result, add [Ltac2 Eval].
        For some reason, Coq can interpret it,
        but the makefile does not work with it.
    *)
    let input := ("<", constr:(B))::("<=", constr:(C))::[] in
    convert_to_chain constr:(A) (Some input) [].

    (* For some reason, [Abort] cannot be called without another
    [Eval] first. Bug in Ltac2? *)
    Ltac2 Eval ().
Abort.

(** * Test 2
    Expected output:
    [
        Chain list = [ChainEnd]
    ]

    TEST NOT AUTOMATED - DO CHECK THE OUTPUT MANUALLY
    (automatic tests are very troublesome 
     with custom types in Ltac2).
    *)
    Lemma test_convert_to_chain_2: forall A B C: Prop, 1=1.
    intros A B C.
    (* To see the result, add [Ltac2 Eval].
        For some reason, Coq can interpret it,
        but the makefile does not work with it.
    *)
    let input := [] in
    convert_to_chain constr:(A) (Some input) [].

    (* For some reason, [Abort] cannot be called without another
    [Eval] first. Bug in Ltac2? *)
    Ltac2 Eval ().
Abort.


(*
--------------------------------------------------------------------------------
*) (** * Testcases for [gen_prop_from_link]
*)
(** * Test 1
    Base case: [Less]
*)
Ltac2 Eval
    let expected := constr:(1 < 2) in
    let link := (constr:(1), Less, constr:(2)) in
    let result := gen_prop_from_link link in
    assert_constr_equal result expected.

(** * Test 2
    Base case: [GreaterEqual]
*)
Ltac2 Eval
    let expected := constr:(1 >= 2) in
    let link := (constr:(1), GreaterEq, constr:(2)) in
    let result := gen_prop_from_link link in
    assert_constr_equal result expected.


Open Scope R_scope.

(* Example of what kinds of problems the tactic is supposed to solve. *)
Lemma non_tactic_example: forall a b c: R, (a < b < c) -> (a < c).
    intros a b c h.
    destruct h as [h1 h2].
    apply (Rlt_le_trans a b c h1).
    apply Rlt_le.
    assumption.
Qed.

(* Simpler way to solve same problem. Is shorter! *)
Lemma non_tactic_example2: forall a b c: R, (a < b < c) -> (a < c).
    intros a b c h.
    destruct h as [h1 h2].
    apply (Rlt_trans a b c h1).
    assumption.
Qed.

(*
--------------------------------------------------------------------------------
*) (** * Testcases for [rewrite_chain]
*)


(** * Test 1
    Base case: got goal [a < c],
    use [a < b < c] to finish goal.
*)
Lemma test_rewrite_chain_1: forall a b c: R, (a < b < c) -> (a < c).
    intros a b c h.
    destruct h as [h1 h2].
    let chain := (
        (ChainLink (constr:(a), Less, constr:(b)))
        ::(ChainLink (constr:(b), Less, constr:(c)))
        ::ChainEnd::[])
    in
    rewrite_chain chain.
Qed.

(** * Test 2
    Base case: got goal [a < c],
    use [a < b] to rewrite goal to [b <= c].
*)
Lemma test_rewrite_chain_2: forall a b c: R, (a < b) -> (a < c).
    intros a b c h.
    let chain := (
        (ChainLink (constr:(a), Less, constr:(b)))
        ::ChainEnd::[])
    in
    rewrite_chain chain.
    assert_constr_equal constr:(b <= c) (Control.goal ()).
Abort.

(** * Test 3
    Base case: Same as Test 1, but with inequality.
    Got goal [a <= c],
    use [a <= b <= c] to finish goal.
*)
Lemma test_rewrite_chain_3: forall a b c: R, (a <= b <= c) -> (a <= c).
    intros a b c h.
    destruct h as [h1 h2].
    let chain := (
        (ChainLink (constr:(a), LessEq, constr:(b)))
        ::(ChainLink (constr:(b), LessEq, constr:(c)))
        ::ChainEnd::[])
    in
    rewrite_chain chain.
Qed.

(** * Test 4
    Base case: Same as Test 2, but with inequality.
    Got goal [a <= c],
    use [a <= b] to rewrite goal to [b <= c].
*)
Lemma test_rewrite_chain_4: forall a b c: R, (a <= b) -> (a <= c).
    intros a b c h.
    let chain := (
        (ChainLink (constr:(a), LessEq, constr:(b)))
        ::ChainEnd::[])
    in
    rewrite_chain chain.
    assert_constr_equal constr:(b <= c) (Control.goal ()).
Abort.

(** * Test 5
    Base case: Same as Test 1, but with equality.
    Got goal [a = c],
    use [a = b = c] to finish goal.
*)
Lemma test_rewrite_chain_5: forall a b c: R, (a = b /\ b = c) -> (a = c).
    intros a b c h.
    destruct h as [h1 h2].
    let chain := (
        (ChainLink (constr:(a), Eq, constr:(b)))
        ::(ChainLink (constr:(b), Eq, constr:(c)))
        ::ChainEnd::[])
    in
    rewrite_chain chain.
Qed.

(** * Test 6
    Base case: Same as Test 1, but with >.
    Got goal [a > c],
    use [a > b > c] to finish goal.
*)
Lemma test_rewrite_chain_6: forall a b c: R, (a > b /\ b > c) -> (a > c).
    intros a b c h.
    destruct h as [h1 h2].
    let chain := (
        (ChainLink (constr:(a), Greater, constr:(b)))
        ::(ChainLink (constr:(b), Greater, constr:(c)))
        ::ChainEnd::[])
    in
    rewrite_chain chain.
Qed.

(** * Test 7
    Base case: Same as Test 2, but with >=.
    Got goal [a >= c],
    use [a >= b] to rewrite goal to [b >= c].
*)
Lemma test_rewrite_chain_7: forall a b c: R, (a >= b) -> (a >= c).
    intros a b c h.
    let chain := (
        (ChainLink (constr:(a), GreaterEq, constr:(b)))
        ::ChainEnd::[])
    in
    rewrite_chain chain.
    assert_constr_equal constr:(b >= c) (Control.goal ()).
Abort.

(** * Test 8.
    Got goal [a = c],
    use [a = b] to rewrite goal to [a <= b].
*)
Lemma test_rewrite_chain_8: forall a b c: R, (a = b) -> (a <= b ).
    intros a b c h.
    (* tactic should do these two:  *)
    (* apply Req_le;assumption. *)
    let chain := (
        (ChainLink (constr:(a), Eq, constr:(b)))
        ::ChainEnd::[])
    in
    rewrite_chain chain.
Qed.

(** * Test 9
    Error case:
    Got goal [a > d],
    Cannot use [a < b < c < d] to finish goal.
*)
Lemma test_rewrite_chain_9: forall a b c d: R, (a < b /\ b < c /\ c < d) -> (a > d).
    intros a b c d h.
    destruct h as [h1 h2].
    destruct h2 as [h2 h3].
    let chain := (
        (ChainLink (constr:(a), Less, constr:(b)))
        ::(ChainLink (constr:(b), Less, constr:(c)))
        ::(ChainLink (constr:(c), Less, constr:(d)))
        ::ChainEnd::[])
    in
    let result () := rewrite_chain chain in
    assert_raises_error result.
Abort.

(** * Test 10
    base case:
    Got goal [a < d],
    Use [a < b < c < d] to finish goal.
*)
Lemma test_rewrite_chain_10: forall a b c d: R, (a < b /\ b < c /\ c < d) -> (a < d).
    intros a b c d h.
    destruct h as [h1 h2].
    destruct h2 as [h2 h3].
    let chain := (
        (ChainLink (constr:(a), Less, constr:(b)))
        ::(ChainLink (constr:(b), Less, constr:(c)))
        ::(ChainLink (constr:(c), Less, constr:(d)))
        ::ChainEnd::[])
    in
    rewrite_chain chain.
Qed.

(** * Test 11

    Same as test 10, but now using > i.o. <.
    base case:
    Got goal [a < d],
    Use [a < b < c < d] to finish goal.
*)
Lemma test_rewrite_chain_11: forall a b c d: R, (a > b /\ b > c /\ c > d) -> (a > d).
    intros a b c d h.
    destruct h as [h1 h2].
    destruct h2 as [h2 h3].
    let chain := (
        (ChainLink (constr:(a), Greater, constr:(b)))
        ::(ChainLink (constr:(b), Greater, constr:(c)))
        ::(ChainLink (constr:(c), Greater, constr:(d)))
        ::ChainEnd::[])
    in
    rewrite_chain chain.
Qed.

(** * Test 12
    Corner case: can prove goal in 1 step. 
    Got goal [a < c],
    use [a < b] to rewrite goal to [b <= c].
*)
Lemma test_rewrite_chain_12: forall a b: R, (a < b) -> (a < b).
    intros a b h.
    let chain := (
        (ChainLink (constr:(a), Less, constr:(b)))
        ::ChainEnd::[])
    in
    rewrite_chain chain.
Qed.

(** * Test 13
    Corner case: mixed equality and inequalities.
    Got goal [a < d],
    Use [a < b = c < d] to finish goal.
*)
Lemma test_rewrite_chain_13: forall a b c d: R, (a < b /\ b = c /\ c < d) -> (a < d).
    intros a b c d h.
    destruct h as [h1 h2].
    destruct h2 as [h2 h3].
    let chain := (
        (ChainLink (constr:(a), Less, constr:(b)))
        ::(ChainLink (constr:(b), Eq, constr:(c)))
        ::(ChainLink (constr:(c), Less, constr:(d)))
        ::ChainEnd::[])
    in
    rewrite_chain chain.
Qed.

(** * Test 14
    Corner case: mixed equality and inequalities.
    Got goal [a < d],
    Use [a = b = c < d] to finish goal.
*)
Lemma test_rewrite_chain_14: forall a b c d: R, (a = b /\ b = c /\ c < d) -> (a < d).
    intros a b c d h.
    destruct h as [h1 h2].
    destruct h2 as [h2 h3].
    let chain := (
        (ChainLink (constr:(a), Eq, constr:(b)))
        ::(ChainLink (constr:(b), Eq, constr:(c)))
        ::(ChainLink (constr:(c), Less, constr:(d)))
        ::ChainEnd::[])
    in
    rewrite_chain chain.
Qed.

(*
--------------------------------------------------------------------------------
*) (** * Testcases for [Rewrite inequality]

    This is a subset of the testcases for [rewrite_chain],
    using the same numbers.
*)
(** * Test 1
    Base case: got goal [a < c],
    use [a < b < c] to finish goal.
*)
Lemma test_rewrite_ineq_1: forall a b c: R, (a < b < c) -> (a < c).
    intros a b c h.
    destruct h as [h1 h2].
    Rewrite inequality a "<" b "<" c.
Qed.

(** * Test 5
    Base case: Same as Test 1, but with equality.
    Got goal [a = c],
    use [a = b = c] to finish goal.
*)
Lemma test_rewrite_ineq_5: forall a b c: R, (a = b /\ b = c) -> (a = c).
    intros a b c h.
    destruct h as [h1 h2].
    Rewrite equality a "=" b "=" c.
Qed.


(** * Test 6
    Base case: Same as Test 1, but with >.
    Got goal [a > c],
    use [a > b > c] to finish goal.
*)
Lemma test_rewrite_ineq_6: forall a b c: R, (a > b /\ b > c) -> (a > c).
    intros a b c h.
    destruct h as [h1 h2].
    Rewrite inequality a ">" b ">" c.
Qed.

(** * Test 7
    Base case: Same as Test 2, but with >=.
    Got goal [a >= c],
    use [a >= b] to rewrite goal to [b >= c].
*)
Lemma test_rewrite_chain_7: forall a b c: R, (a >= b) -> (a >= c).
    intros a b c h.
    Rewrite inequality a "≥" b.
    assert_constr_equal constr:(b >= c) (Control.goal ()).
Abort.

(** * Test 13
    Corner case: mixed equality and inequalities.
    Got goal [a < d],
    Use [a < b = c < d] to finish goal.
*)
Lemma test_rewrite_ineq_13: 
    forall a b c d: R, (a < b /\ b = c /\ c < d) -> (a < d).
    intros a b c d h.
    destruct h as [h1 h2].
    destruct h2 as [h2 h3].
    Rewrite inequality a "<" b "=" c "<" d.
Qed.