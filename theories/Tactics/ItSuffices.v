(******************************************************************************)
(*                  This file is part of Waterproof-lib.                      *)
(*                                                                            *)
(*   Waterproof-lib is free software: you can redistribute it and/or modify   *)
(*    it under the terms of the GNU General Public License as published by    *)
(*     the Free Software Foundation, either version 3 of the License, or      *)
(*                    (at your option) any later version.                     *)
(*                                                                            *)
(*     Waterproof-lib is distributed in the hope that it will be useful,      *)
(*      but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*       MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the         *)
(*               GNU General Public License for more details.                 *)
(*                                                                            *)
(*     You should have received a copy of the GNU General Public License      *)
(*   along with Waterproof-lib. If not, see <https://www.gnu.org/licenses/>.  *)
(*                                                                            *)
(******************************************************************************)

Require Import Ltac2.Ltac2.

Require Import Util.Init.
Require Import Waterprove.

Ltac2 Type exn ::= [ AutomationFailure(string) ].

Local Ltac2 raise_automation_failure () :=
  Control.zero (AutomationFailure "Waterproof could not verify that this statement is enough to prove the goal.").

(**
  Execute a function [f] (assuming it contains an expression that applies the [enough ... by ...] tactic).
  
  If it succeeds, print that [statement] is sufficient to show the goal. Raise an error if [f] also does.

  Arguments:
    - [f: unit -> unit], expression applying the tactic [enough ... by ...].
    - [statement: constr], statement that was 'enough'  evidence to proof the goal. Only used for printing purposes.
    
  Raises exceptions:
    - [AutomationFailure], in case [f] throws an error.
      This typically happens if the [enough ... by ...]-expression fails to prove the goal.
*)
Local Ltac2 try_enough_expression (f: unit -> unit) (statement: constr) :=
  match Control.case f with
    | Val _ => ()
    | Err exn => raise_automation_failure ()
  end.

(**
  Try if the [waterprove] automation would be able to solve the current goal, if [statement] were to hold.
  
  If it succeeds, the goal is removed, and proving [statement] is added as a new goal. If it fails, an error will be raised.

  Arguments:
    - [statement: constr], statement to assume to hold (and to be proven later).
    - [proving_lemma: constr], lemma that can help in the proof
    
  Raises exceptions:
    - [AutomationFailure], in case [waterprove] fails to prove the goal, even if [statement] is given.
*)
Ltac2 apply_enough_with_waterprove (statement:constr) (proving_lemma: constr option) :=
  let hyp_name := Fresh.in_goal @h in
  let f () := enough ($hyp_name : $statement) by (
    match proving_lemma with
      | None => waterprove 5 true [] Positive
      | Some lemma => rwaterprove 5 true [fun () => lemma] Positive [lemma] []
    end
  ) in
  try_enough_expression f statement.

(**
  Same as the function [apply_enough_with_waterprove].

  Take [statement] as a given fact, and try to prove the current goal automatically with it.
    
  If it succeeds, the goal is removed, and proving [statement] is added as a new goal. If it fails, an error will be raised.

  Arguments:
    - [statement: constr], statement to assume to hold (and to be proven later).
    
  Raises exceptions:
    - [AutomationFailure], in case no proof is found for the goal, even if [statement] is given.
*)
Ltac2 Notation "It" "suffices" "to" "show" "that" statement(constr) := 
  apply_enough_with_waterprove statement None.

(**
  Same as "It suffices to show that" except it adds an additional lemma temporarily to the underlying automation.

  Arguments:
    - [statement: constr], statement to assume to hold (and to be proven later).
    - [lemma: constr], lemma that can help in the proof
    
  Raises exceptions:
    - [AutomationFailure], in case no proof is found for the goal, even if [statement] is given.
*)
Ltac2 Notation "By" lemma(constr) "it" "suffices" "to" "show" "that" statement(constr) :=
  apply_enough_with_waterprove statement (Some lemma).