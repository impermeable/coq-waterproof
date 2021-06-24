(** * proof_finishing_tactics.v
Authors: 
    - Cosmin Manea (1298542)
    - Lulof Pirée (1363638)

Creation date: 06 June 2021

Several tactics to finish a proof at the point
where it has become trivial
(e.g. when there is an assumption that states the goal,
or when the goal has the form [X = X]).
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
From Ltac2 Require Import Option.
From Ltac2 Require Import Message.

Require Import Waterproof.tactics.forward_reasoning.we_conclude_that.
Require Import Waterproof.test_auxiliary.

    
(** * This follows by reflexivity
    Simply call [reflexivity],
    raise a custom error in case of failure.
*)
Ltac2 Type exn ::= [ ReflexivityError(string) ].
Ltac2 Notation "This" "follows" "by" "reflexivity" :=
    let result () := reflexivity in
    match Control.case result with
    | Val _ => ()
    | Err enx => 
        Control.zero (ReflexivityError 
        "Reflexivity cannot be applied here.")
    end.

(** * This follows by assumption
    Simply call [assumption],
    raise a custom error in case of failure.
*)
Ltac2 Type exn ::= [ AssumptionError(string) ].
Ltac2 Notation "This" "follows" "by" "assumption" :=
    let result () := assumption in
    match Control.case result with
    | Val _ => ()
    | Err enx => 
        Control.zero (AssumptionError 
        "No hypothesis found that equals the current goal.")
    end.

(** * This concludes the proof
    Tries to complete proving the goal under focus.
    Same as [We conclude that ...],
    but without checking if the user supplied the correct proof.
*)
Ltac2 Notation "This" "concludes" "the" "proof" :=
    print (of_string "Recommended: make explicit what you conclude,
by using 'We conclude that ...`.");
    solve_remainder_proof (Control.goal ()) None.


Ltac2 Notation "This" "follows" "immediately" := 
    solve_remainder_proof (Control.goal ()) None.

(** * Then ... holds by assumption
    Try to prove the goal with the fact 
    that a hypothesis (supposedly) exists that states the goal.

    Arguments:
        - [target_goal: constr], expression that should equal
            the definition of the goal.
    
    Raises exceptions:
        - [AutomationFailure], if [target_goal] is not logically equivalent
            to the actual goal under focus. 
            Only print a warning in case 
            [target_goal] is logically equivalent,
            but not directly equivalent without rewriting.
        - [AssumptionError], if there is no hypothesis that has the same
            type as the goal.
*)
Ltac2 Notation "Then" target_goal(constr) "holds" "by" "assumption" :=
    let call_assumption () := This follows by assumption in    
    check_goal_and_call target_goal call_assumption.



