(** * [we_need_to_show.v]
Authors: 
    - Lulof Pirée (1363638)
    - Jelle Wemmenhove

Creation date: 18 May 2021
Latest edit:   12 Oct  2021

Tactic that checks if the user input matches the goal.
Does not proceed the proof;
only helps for proof readability.

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

Require Import Waterproof.auxiliary.
Require Import Waterproof.tactics.goal_wrappers.
Require Import Waterproof.tactics.unfold.


Ltac2 Type exn ::= [ GoalCheckError(string) ].

Ltac2 raise_goal_check_error (s:string) := 
    Control.zero (GoalCheckError s).

(** * check_goal
    Check if the type of the goal is syntactically equal to [t].

    Arguments:
        - [t: constr], any constr to be compared against the goal.

    Does:
        - Prints a confirmation that the goal equals the provided type.
    
    Raises Exceptions:
        - [GoalCheckError], if the goal is not syntactically equal to [t].
*)
Local Ltac2 check_goal := fun (t:constr) =>
    lazy_match! goal with
    | [ |- ?g] => 
        match Aux.check_constr_equal g t with
        | true => print (concat 
                    (of_string "The goal is indeed: ") (of_constr t))
        | false => raise_goal_check_error "No such goal"
        end
    | [|-_] => raise_goal_check_error "No such goal"
    end.

(** * check_and_change_goal
    Check if the type of the goal is convertible to [t],
    if so, it replaces the goal by t.

    Arguments:
        - [t: constr], any constr to be compared against the goal.

    Does:
        - Prints a confirmation that the goal equals the provided type.
    
    Raises Exceptions:
        - [GoalCheckError], if the goal is not convertible to [t].
*)
Local Ltac2 check_and_change_goal := fun (t:constr) =>
    lazy_match! goal with
    | [ |- ?g] => 
        match Aux.check_constr_equal g t with
        | true => print (concat 
                    (of_string "The goal is indeed: ") (of_constr t));
                  change $t
        | false => raise_goal_check_error "No such goal"
        end
    | [|-_] => raise_goal_check_error "No such goal"
    end.

(** * to_show
    1) If the goal is wrapped in ExpandDef.Goal.Wrapper, attempt to remove the wrapper.
    2) Else, check if the type of the goal is convertible to [t],
      if so, it replaces the goal by t.

    Arguments:
        - [t: constr], 1) type matching the current wrapped goal.
                       2) any constr to be compared against the goal.

    Does:
        - 1) Removes the wrapper if the argument matches the wrapped goal, 
               i.e. the goal is of the form [ExandDef.Goal.Wrapper t].
          2) Prints a confirmation that the goal equals the provided type.
    
    Raises Exceptions:
        - 1) [ExpandDefError], if the argument [t] does not match the wrapped goal.
        - 2) [GoalCheckError], if the goal is not convertible to [t].
*)
Local Ltac2 unwrap_or_check_and_change_goal (t : constr) :=
    lazy_match! goal with
    | [|- ExpandDef.Goal.Wrapper _] => goal_as t (*[goal_as] is from unfold.v*)
    | [|- _] => check_and_change_goal t
    end.

(* Allow different syntax styles:
    - We need to show ...
    - We need to show that ...
    - We need to show : ...
    - We need to show that : ...
    - To show ...
    - To show that ...
    - To show : ...
    - To show that : ...

    Optional string keywords do need to have a name,
    even though the parser will not populate this name. 
    (That's why it reads "that(opt('that'))" instead of "opt('that')".*)
Ltac2 Notation "We" "need" "to" "show" that(opt("that")) colon(opt(":")) t(constr) :=
      unwrap_or_check_and_change_goal t.

Ltac2 Notation "To" "show" that(opt("that")) colon(opt(":")) t(constr) :=
      unwrap_or_check_and_change_goal t.

