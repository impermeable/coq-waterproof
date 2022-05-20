(** * [goal_to_hint.v]
Authors: 
    - Lulof Pirée (1363638)
Creation date: 2 June 2021

[Check status] prints a hint to the user how to tackle the rest of the proof.

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
Require Import Waterproof.auxiliary.
Require Import Waterproof.tactics.goal_wrappers.

Ltac2 Type exn ::= [ GoalHintError(string) ].

Local Ltac2 create_forall_message (v_type: constr) :=
  Message.concat
            (Message.concat
                (Message.of_string "The goal is to show a ‘for all’-statement (∀).
Introduce an arbitrary variable of type ")
                (Message.of_constr v_type)
            )
            ( Message.of_string ".
Use ‘Take ... : ...’.").

Local Ltac2 create_implication_message (premise: constr) :=
    Message.concat
        (Message.concat
            (Message.of_string "The goal is to show an implication (⇒).
Assume the premise ")
            (Message.of_constr premise)
        )
        ( Message.of_string ".
Use ‘Assume that (...).’.").

Local Ltac2 create_function_message (premise: constr) :=
    Message.concat
        (Message.concat
            (Message.of_string "The goal is to construct a map (⇒).
Introduce an arbitrary variable of type ")
                (Message.of_constr premise)
            )
            ( Message.of_string ".
Use ‘Take ... : ...’.").

Local Ltac2 create_exists_message (premise: constr) :=
    Message.concat
        (Message.concat
            (Message.of_string "The goal is to show a ‘there exists’-statement (∃).
Choose a specific variable of type ")
                (Message.of_constr premise)
        )
        ( Message.of_string ".
Use ‘Choose ... ’.").

Local Ltac2 create_goal_wrapped_message () :=
    Message.of_string "Follow the advice in the goal window.".

Local Ltac2 create_not_message (negated_type : constr) := 
  Message.concat
     (Message.concat
         (Message.concat
             (Message.of_string "The goal is to show a negation (¬).
Assume that the negated expression ") (Message.of_constr negated_type)) 
(Message.of_string " holds, then show a contradiction."))
(Message.of_string "
Use ‘Assume that (...).’ to do the first step.").

Local Ltac2 create_contradiction_message () :=
    Message.of_string "The goal is to show a contradiction. 
Show two properties that contradict eachother, i.e. prove P and (¬ P) for some P.
Initiate the proof of a new property by using ‘We claim that (...).’.
Use ‘Contradiction.’ or ‘↯.’ after you have shown two contradictory properties.".

(** * goal_to_hint
    Give a hint indicating a potential step to proving 
    a given proposition [g].

    Arguments:
        - [g : constr], should be a [Prop], 
            namely the goal to provide hints for.
    
    Returns:
        - [message], message containing a hint.

    Raises exceptions:
        - [GoalHintError], if no hint is available for [g].
*)
Ltac2 goal_to_hint (g:constr) :=
    (* The order matters. 
        If the ∀ case is above the ⇒,
        then implications will fire the ∀ case instead.*)
    lazy_match! g with
    | context [?a -> ?b]  => 
        let sort_a := Aux.get_value_of_hyp a in
        match Aux.check_constr_equal sort_a constr:(Prop) with
        | true  => create_implication_message a
        | false => create_function_message a
        end
    | context [forall v:?v_type, _]  => create_forall_message v_type
    | context [exists v:?v_type, _]  => create_exists_message v_type
    | context [Case.Wrapper _ _]                => create_goal_wrapped_message ()
    | context [NaturalInduction.Base.Wrapper _] => create_goal_wrapped_message ()
    | context [NaturalInduction.Step.Wrapper _] => create_goal_wrapped_message ()
    | context [ExpandDef.Goal.Wrapper _]        => create_goal_wrapped_message ()
    | context [ExpandDef.Hyp.Wrapper _ _ _]     => create_goal_wrapped_message ()
    | context [StateGoal.Wrapper _]             => create_goal_wrapped_message ()
    | context [not ?g] => create_not_message g
    | context [False]  => create_contradiction_message ()
    | _ => Control.zero (GoalHintError "No hint available for this goal.")
    end.

(** * print_goal_hint
    Print a hint indicating a potential step to proving 
    the current goal (if the goal is a ∀, ⇒ or ∃ proposition).
    When no hint is available, print "No hint available".

    Arguments:
        - [g: constr option], optional goal to generate hint for.
            If [None] is given, then uses currently active goal.
*)
Ltac2 print_goal_hint (g: constr option) :=
    let g' := 
        match g with
        | None => Control.goal ()
        | Some y => y
        end
    in
    let f () := goal_to_hint g' in
    match Control.case f with
    | Val mess => 
        match mess with
        | (mess, _) => Message.print mess
        | _ => ()
        end
    | Err exn => Message.print (Message.of_string "No hint available.")
    end.

(** * Help tactic
    Tries to give a hint how to proceed proving the current goal.
*)
Ltac2 Notation "Help" := print_goal_hint None.


