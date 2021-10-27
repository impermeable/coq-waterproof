(** * [it_suffices_to_show.v]
Authors: 
    - Lulof Pirée (1363638)
    - Jim Portegies
Creation date: 6 June 2021

Tactic [It suffices to show that ...].
Used to assert that a certain statement would be able to prove the goal.
After that, one still needs to prove this statement, but not the original goal.
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

Require Import Waterproof.tactics.forward_reasoning.forward_reasoning_aux.
Require Import Waterproof.tactics.goal_wrappers.

Local Ltac2 fail_suffice_to_show () :=
    Control.zero (AutomationFailure 
"Waterproof could not verify that this statement is enough to prove the goal.").

(** * try_enough_expression
    Execute a function [f] (assuming it contains
    an expression that applies the [enough ... by ...] tactic).
    If it succeeds, print that [statement] is sufficient to show the goal.
    Raise an error if [f] also does.

    Arguments:
        - [f: unit -> unit], expression applying the tactic [enough ... by ...].
        - [statement: constr], statement that was 'enough' 
            evidence to proof the goal. Only used for printing purposes.
    
    Raises exceptions:
        - [AutomationFailure], in case [f] throws an error.
            This typically happens if the [enough ... by ...]-expression fails
            to prove the goal.
*)
Local Ltac2 try_enough_expression (f: unit -> unit) 
                           (statement: constr):=
    match Control.case f with
    | Val _ => 
    print (
        concat
            (of_string "It indeed suffices to show that '")
            (concat 
                (of_constr statement)
                (of_string "'.")
            )
    )
    | Err exn => fail_suffice_to_show ()
    end.

(** * apply_enough_with_waterprove
    Try if the [waterprove] automation would be able to solve
    the current goal, if [statement] were to hold.
    If it succeeds, the goal is removed, 
    and proving [statement] is added as a new goal.
    If it fails, an error will be raised.

    Arguments:
        - [statement: constr], statement to assume to hold
            (and to be proven later).
        - [proving_lemma: constr], lemma that can help in the proof
    
    Raises exceptions:
        - [AutomationFailure], in case [waterprove] fails to prove the goal,
            even if [statement] is given.
*)
Ltac2 apply_enough_with_waterprove (statement:constr) (proving_lemma: constr option) :=
    let help_lemma := unwrap_optional_lemma proving_lemma
    in
    let g := Control.goal () in
    let hyp_name := Fresh.in_goal @h in
    let f () := enough ($hyp_name : $statement) 
                by (waterprove_with_hint g help_lemma)
    in
    try_enough_expression f statement.

(** * It suffices to show that ...
    Same as the function [apply_enough_with_waterprove].

    Take [statement] as a given fact, 
    and try to prove the current goal automatically with it.
    If it succeeds, the goal is removed, 
    and proving [statement] is added as a new goal.
    If it fails, an error will be raised.

    Arguments:
        - [statement: constr], statement to assume to hold
            (and to be proven later).
    
    Raises exceptions:
        - [AutomationFailure], in case no proof is found for the goal,
            even if [statement] is given.
*)
Ltac2 Notation "It" "suffices" "to" "show" "that" statement(constr) := 
    apply_enough_with_waterprove statement None.

(** * By ... it suffices to show that ...
    Same as "It suffices to show that" except it adds an additional lemma 
    temporarily to the underlying automation.

    Arguments:
        - [statement: constr], statement to assume to hold
            (and to be proven later).
        - [lemma: constr], lemma that can help in the proof
    
    Raises exceptions:
        - [AutomationFailure], in case no proof is found for the goal,
            even if [statement] is given.
*)
Ltac2 Notation "By" lemma(constr) "it" "suffices" "to" "show" "that" statement(constr) :=
    apply_enough_with_waterprove statement (Some lemma).

(*

(** * apply_enough_with_tactic
    Take [statement] as a given fact, 
    and try to prove the current goal using the specified tactic(s) [tac].
    If it succeeds, the goal is removed, 
    and proving [statement] is added as a new goal.
    If it fails, an error will be raised.

    Arguments:
        - [statement: constr], statement to assume to hold
            (and to be proven later).
        - [tac: unit -> unit], expression containing a tactic
            that is supposed to prove the current goal 
            (usually using [statement] as a hypothesis).
            This can be a concatenation of tactics enclosed in [(] and [])]
            separated by [;]. E.g. [tac := (apply some_lemma;assumption)].
    
    Raises exceptions:
        - [AutomationFailure], in case evaluating [tac] does not prove the goal,
            even if [statement] is given.
*)
Ltac2 apply_enough_with_tactic (statement:constr) (tac:unit -> unit) :=
    let hyp_name := Fresh.in_goal @h in
    let f () := enough ($hyp_name : $statement) by (tac ())
    in
    try_enough_expression f statement.

(** * It suffices to show that ... by ...
    Same as the function [apply_enough_with_tactic].

    Take [statement] as a given fact, 
    and try to prove the current goal using the specified tactic(s) [tac].
    If it succeeds, the goal is removed, 
    and proving [statement] is added as a new goal.
    If it fails, an error will be raised.

    Arguments:
        - [statement: constr], statement to assume to hold
            (and to be proven later).
        - [tac: unit -> unit], expression containing a tactic
            that is supposed to prove the current goal 
            (usually using [statement] as a hypothesis).
            This can be a concatenation of tactics enclosed in [(] and [])]
            separated by [;]. E.g. [tac := (apply some_lemma;assumption)].
    
    Raises exceptions:
        - [AutomationFailure], in case evaluating [tac] does not prove the goal,
            even if [statement] is given.
*)

Ltac2 Notation "It" "suffices" "to" "show" "that" statement(constr)
                "by" tac(thunk(tactic)) := 
    panic_if_goal_wrapped ();
    apply_enough_with_tactic statement tac.


*)