(** * [we_conclude_that.v]
Authors: 
    - Lulof Pirée (1363638)
Creation date: 6 June 2021

Tactic [We conclude that ...].
Used to finish the proof of an (intermediate) goal.

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

Require Import Rbase.
Require Import Qreals.
Require Import Rfunctions.
Require Import SeqSeries.
Require Import Rtrigo.
Require Import Ranalysis.
Require Import Integration.
Require Import micromega.Lra.
Require Import Omega.
Require Import Max.

Require Import Sets.Ensembles.
Require Import Sets.Classical_sets.


Require Import Waterproof.tactics.forward_reasoning.forward_reasoning_aux.
Require Import Waterproof.waterprove.waterprove.
Require Import Waterproof.tactics.goal_wrappers.

Ltac2 warn_equivalent_goal_given () :=
    print (of_string "Warning: 
The statement you provided does not exactly correspond to what you need to show. 
This can make your proof less readable.
Waterproof will try to rewrite the goal...").

Ltac2 warn_wrong_goal_given (wrong_target: constr) :=
    print (concat
            (concat
                (concat
                    (of_string "The actual goal (")
                    (of_constr (Control.goal ()))
                )
                (concat 
                    (of_string ") is not equivalent to the goal you gave (")
                    (of_constr wrong_target)
                )
            )
            (of_string "). ")
    ).

(** * target_equals_goal_judgementally
    Check if [target] is judgementally (i.e. by rewriting definitions)
    equal to the goal.

    Arguments:
        - [target:constr], expression to compare to goal.

    Returns:
        - [bool],
            - [true], if [target] is judgementally equal 
                to the goal under focus.
            - [false], otherwise.
*)
Ltac2 target_equals_goal_judgementally (target:constr) :=
    let target := eval cbv in $target in
    let real_goal := Control.goal () in
    let real_goal := eval cbv in $real_goal in
    Constr.equal target real_goal.


(** * check_goal_and_call
    Check if the current goal is equivalent to [target_goal],
    and call a function [callback] if they are.
    Raise a warning if they are logically equivalent,
    but one needs to be rewritten first.
    Throw an error if the current goal is not logically
    equivalent to [target_goal].
    
    Arguments:
        - [target_goal: constr], expression that 
            should equal the goal under focus.
        - [callback: unit -> unit], Ltac2 function
            to call in case the goal is correct.

    Raises exceptions:
        - [AutomationFailure], if [target_goal] is not equivalent
            to the actual goal under focus, even after rewriting.
        - Any exception raised by [callback].
*)
Ltac2 check_goal_and_call (target_goal:constr) (callback: unit -> unit) :=
    (* First check if the given target equals the goal directly,
    without applying any rewrite. *)
    match Constr.equal target_goal (Control.goal ()) with
    | false => 
        match target_equals_goal_judgementally target_goal with
        | false => 
            warn_wrong_goal_given (target_goal); 
            Control.zero (AutomationFailure 
        "Given goal not equivalent to actual goal.")
        | true => 
            (* User provided an equivalent goal, 
            but written differently. 
            Try to rewrite the real goal to match user input.*)
            warn_equivalent_goal_given ();
            let g := Control.goal () in
            change $target_goal;
            callback ()
        end
    | true => callback ()
    end.
    
(** * solve_remainder_proof
    Check if the given [target_goal] equals the actual goal under focus.
    If they are different, raise an error.
    If they are equivalent after rewriting, raise an error and continue.
    If the [target_goal] is equivalent to the goal under focus,
    finish the proof automatically with the given lemma.

    Arguments:
        - [target_goal: constr], expression that 
            should equal the goal under focus.
        - [lemma: constr option], optional lemma to include in the
            automatic proof completion ([waterprove]).
    
    Raises exceptions:
        - [AutomationFailure], if [waterprove] fails the prove the goal
            (I.e. the goal is too difficult, or does not hold).
        - [AutomationFailure], if [target_goal] is not equivalent
            to the actual goal under focus, even after rewriting.
*)
Ltac2 solve_remainder_proof (target_goal:constr) (lemma:constr option) :=
    let lemma := unwrap_optional_lemma lemma in
    let finish_proof () := waterprove_without_hint target_goal lemma in
    check_goal_and_call target_goal finish_proof.


(** * We conclude that ...
    Finish proving a goal using automation.

    Arguments:
        - [target_goal: constr], expression that 
            should equal the goal under focus.
        - [lemma: constr option], optional lemma to include in the
            automatic proof completion ([waterprove]).

    Raises exceptions:
        - [AutomationFailure], if [waterprove] fails the prove the goal
            (I.e. the goal is too difficult, or does not hold).
        - [AutomationFailure], if [target_goal] is not equivalent
            to the actual goal under focus, even after rewriting.
*)
Ltac2 Notation "We" "conclude" "that" target_goal(constr) := 
    panic_if_goal_wrapped ();
    solve_remainder_proof target_goal None.

(** * It follows that ...
    Alternative notation for [We conclude that ...].
*)
Ltac2 Notation "It" "follows" "that" target_goal(constr) :=  
    panic_if_goal_wrapped ();
    solve_remainder_proof target_goal None.

(** * We conclude that ...
    Finish proving a goal using automation.

    Arguments:
        - [target_goal: constr], expression that 
            should equal the goal under focus.

    Raises exceptions:
        - [AutomationFailure], if [waterprove] fails the prove the goal
            (I.e. the goal is too difficult, or does not hold).
        - [AutomationFailure], if [target_goal] is not equivalent
            to the actual goal under focus, even after rewriting.
*)
Ltac2 Notation "By" lemma(constr) "we" "conclude" "that" target_goal(constr) :=  
    panic_if_goal_wrapped ();
    solve_remainder_proof target_goal (Some lemma).