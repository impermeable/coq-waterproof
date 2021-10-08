(** * [write_using.v]
Authors: 
    - Lulof Pirée (1363638)
Creation date: 08 June 2021

Contains tactics [Write goal using ...] and [Write ... using ...].
Used to rewrite and finish the goal/hypothesis with a certain equality,
which is then set as a new goal.
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

Require Import Waterproof.tactics.forward_reasoning.rewrite_using.
Require Import Waterproof.auxiliary.
Require Import Waterproof.tactics.goal_wrappers.

(** * print_expcted_actual_result
    Print a message showing the expected and actual
    result of a rewrite.

    Arguments:
        - [expected: constr], the expected result of the rewrite.
        - [actual: constr], the actual result of the rewrite.
*)
Local Ltac2 print_expcted_actual_result (expected: constr)
                                        (actual: constr) :=
    print (concat
        (concat
            (concat
                (of_string "Expected result of rewrite: '")
                (of_constr expected)
            )
            (of_string "'.
")
        )
        (concat
            (concat 
                (of_string "Actual result: '")
                (of_constr actual)
            )
            (of_string "'.")
        )
    ).

(** * check_hyp_type_no_normalization
    Check if a hypothesis of the the expected type.
    Raise an error and print the difference if they are not equal.
    Does not perform normalization on the arguments.

    Arguments:
        - [actual: constr], the actual type of hypothsis.
        - [expected: constr], the expected type of hypothsis.

    Raises exceptions:
        - [RewriteError], if [actual] is not equal to [expected].
*)
Local Ltac2 check_hyp_type_no_normalization (actual: constr) 
                                            (expected: constr) :=
    match Constr.equal actual expected with
    | true => ()
    | false => print_expcted_actual_result expected actual;
        Control.zero (RewriteError 
    "Rewriting the hypothesis with this equality is possible,
but did produce the expected result")
    end.

(** * write_id_using_prop_as_expected
    Rewrite an hypothesis identified by [id],
    using a litteral proposition [prop],
    into the [expected] form.
    Raise an error if the reweite resulted in another
    expression than [expected].

    Arguments:
        - [id: ident], name of hypothsis to rewrite.
        - [prop: constr], litteral proposition to use a rewriting rule.
            The expression must be proveable.
        - [expected: constr], expected result of rewrite.

    Raises exceptions:
        - [AutomationFailure], if [prop] could not be proven automatically
            (It may be too difficult to prove, or be incorrect).
        - [RewriteError], if the resulting type 
            of the hypothsis (identified by [id])
            does not equal [expected].
*)
Local Ltac2 write_id_using_prop_as_expected (id: ident) (prop: constr) 
                                            (expected: constr) :=
    rewrite_with_prop_check prop (Some id) false; 
    let result := Aux.get_value_of_hyp_id id in
    check_hyp_type_no_normalization result expected.

(** * Write ... using ... as ...
    Custom notation that directly executes the function 
    [write_id_using_prop_as_expected].

    Rewrite an hypothesis identified by [id],
    using a litteral proposition [prop],
    into the [expected] form.
    Raise an error if the reweite resulted in another
    expression than [expected].

    Arguments:
        - [id: ident], name of hypothsis to rewrite.
        - [prop: constr], litteral proposition to use a rewriting rule.
            The expression must be proveable.
        - [expected: constr], expected result of rewrite.

    Raises exceptions:
        - [AutomationFailure], if [prop] could not be proven automatically
            (It may be too difficult to prove, or be incorrect).
        - [RewriteError], if the resulting type 
            of the hypothsis (identified by [id])
            does not equal [expected].
*)
Ltac2 Notation "Write" id(ident) "using" prop(constr) "as" expected(constr) :=
    panic_if_goal_wrapped ();
    write_id_using_prop_as_expected id prop expected.



(** * write_goal_using_prop_as_expected

    Identical to [write_id_using_prop_as_expected],
    but rewrites the goal instead of a hypothsis.

    Rewrite the goal using a litteral proposition [prop],
    into the [expected] form.
    Raise an error if the reweite resulted in another
    expression than [expected].

    Arguments:
        - [prop: constr], litteral proposition to use a rewriting rule.
            The expression must be proveable.
        - [expected: constr], expected result of rewrite.

    Raises exceptions:
        - [AutomationFailure], if [prop] could not be proven automatically
            (It may be too difficult to prove, or be incorrect).
        - [RewriteError], if the resulting type 
            of goal does not equal [expected].
*)
Local Ltac2 write_goal_using_prop_as_expected (prop: constr) 
                                            (expected: constr) :=
    rewrite_with_prop_check prop None false; 
    let result := Control.goal () in
    check_hyp_type_no_normalization result expected.

(** * Write goal using ... as ...

    Custom notation for the function [write_goal_using_prop_as_expected].

    Rewrite the goal using a litteral proposition [prop],
    into the [expected] form.
    Raise an error if the reweite resulted in another
    expression than [expected].

    Arguments:
        - [prop: constr], litteral proposition to use a rewriting rule.
            The expression must be proveable.
        - [expected: constr], expected result of rewrite.

    Raises exceptions:
        - [AutomationFailure], if [prop] could not be proven automatically
            (It may be too difficult to prove, or be incorrect).
        - [RewriteError], if the resulting type 
            of goal does not equal [expected].
*)
Ltac2 Notation "Write" "goal" "using" prop(constr) "as" expected(constr) :=
    panic_if_goal_wrapped ();
    write_goal_using_prop_as_expected prop expected.