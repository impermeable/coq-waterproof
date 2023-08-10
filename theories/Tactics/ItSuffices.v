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
Require Import Ltac2.Message.

Require Import Util.Init.
Require Import Util.Goals.
Require Import Waterprove.

Ltac2 Type exn ::= [ AutomationFailure(message) ].

Local Ltac2 concat_list (ls : message list) : message :=
  List.fold_right concat (of_string "") ls.


(* Local Ltac2 raise_automation_failure () :=
  Control.zero (AutomationFailure "Waterproof could not verify that this statement is enough to prove the goal."). *)

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
(* Local Ltac2 try_enough_expression (f: unit -> unit) (statement: constr) :=
  match Control.case f with
    | Val _ => ()
    | Err exn => raise_automation_failure ()
  end. *)

(**
  Try if the [waterprove] automation would be able to solve the current goal, if [statement] were to hold.
  
  If it succeeds, the goal is removed, and proving [statement] is added as a new goal. If it fails, an error will be raised.

  Arguments:
    - [statement: constr], statement to assume to hold (and to be proven later).
    - [proving_lemma: constr], lemma that can help in the proof
    
  Raises exceptions:
    - [AutomationFailure], in case [waterprove] fails to prove the goal, even if [statement] is given.
*)
Local Ltac2 wp_enough (new_goal : constr) :=
  let err_msg := concat_list
    [of_string "Could not verify that it suffices to show "; of_constr new_goal; of_string "."] in
  match Control.case (fun () =>
    enough $new_goal by (waterprove 5 true [] Main))
  with
  | Val _ => ()
  | Err exn => Control.zero (AutomationFailure err_msg)
  end.
  
Local Ltac2 wp_enough_by (new_goal : constr) (xtr_lemma : constr) := 
  let err_msg := concat_list
    [of_string "Could not verify that it suffices to show "; of_constr new_goal; of_string "."] in
  match Control.case (fun () =>
    enough $new_goal by 
      (rwaterprove 5 true [fun () => xtr_lemma] Main [xtr_lemma] []))
  with
  | Val _ => ()
  | Err exn => 
    (* check if it would work without lemma *)
    match Control.case (fun () =>
      enough $new_goal by 
        (waterprove 5 true [] Main))
    with
    | Err exn => Control.zero (AutomationFailure err_msg)
    | Val _ =>
      (* problem is the extra lemma: it is not used for proof that new goal is enough *)
      Control.zero (AutomationFailure (concat_list 
        [of_string "Could not verify how this follows from "; of_constr xtr_lemma;
          of_string "."]))
    end
  end.


(**
  Same as the function [apply_enough_with_waterprove].

  Take [statement] as a given fact, and try to prove the current goal automatically with it.
    
  If it succeeds, the goal is removed, and proving [statement] is added as a new goal. If it fails, an error will be raised.

  Arguments:
    - [statement: constr], statement to assume to hold (and to be proven later).
    
  Raises exceptions:
    - [AutomationFailure], in case no proof is found for the goal, even if [statement] is given.
*)
Ltac2 Notation "It" "suffices" "to" "show" that(opt("that")) statement(constr) := 
  panic_if_goal_wrapped ();
  wp_enough statement.

(**
  Same as "It suffices to show that" except it adds an additional lemma temporarily to the underlying automation.

  Arguments:
    - [statement: constr], statement to assume to hold (and to be proven later).
    - [lemma: constr], lemma that can help in the proof
    
  Raises exceptions:
    - [AutomationFailure], in case no proof is found for the goal, even if [statement] is given.
*)
Ltac2 Notation "By" xtr_lemma(constr) "it" "suffices" "to" "show" that(opt("that")) statement(constr) :=
  panic_if_goal_wrapped ();
  wp_enough_by statement xtr_lemma.