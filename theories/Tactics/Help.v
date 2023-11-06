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
Local Ltac2 concat_list (ls : message list) : message :=
  List.fold_right concat (of_string "") ls.

Require Import Util.Constr.
Require Import Util.Goals.
Require Import Util.Hypothesis.
Require Import Util.MessagesToUser.

Require Import Waterprove.

Ltac2 Type exn ::= [ Inner ].

Local Ltac2 create_forall_message (v_type: constr) :=
  concat_list [of_string "The goal is to show a ‘for all’-statement (∀).
Introduce an arbitrary variable of type "; of_constr v_type; of_string ".
Use ‘Take ... : (...).’."].

Local Ltac2 create_implication_message (premise: constr) :=
  concat_list [of_string "The goal is to show an implication (⇒).
Assume the premise "; of_constr premise; of_string ".
Use ‘Assume that (...).’."].

Local Ltac2 create_function_message (premise: constr) :=
  concat_list [of_string "The goal is to construct a map (⇒).
Introduce an arbitrary variable of type "; of_constr premise; of_string ".
Use ‘Take ... : (...).’."].

Local Ltac2 create_exists_message (premise: constr) :=
  concat_list [of_string "The goal is to show a ‘there exists’-statement (∃).
Choose a specific variable of type "; of_constr premise; of_string ".
Use ‘Choose ... := (...).’ or ‘Choose (...).’."].

Local Ltac2 create_goal_wrapped_message () := of_string "Follow the advice in the goal window.".

Local Ltac2 create_not_message (negated_type : constr) := 
  concat_list [of_string "The goal is to show a negation (¬).
Assume that the negated expression "; of_constr negated_type; 
of_string " holds, then show a contradiction.
Use ‘Assume that (...).’ to do the first step."].

(**
  Auxilliary tactic that checks if goal can be shown with automation
*)
Local Ltac2 solvable_by_core_auto () :=
  let temp_id := Fresh.in_goal @temp in
  let goal := Control.goal () in
  assert $goal as $temp_id;
  Control.focus 1 1 (fun () => waterprove 5 true Main);
  clear $temp_id.

(**
  Give a hint indicating a potential step to proving a given proposition [g].

  Arguments:
    - [g : constr], should be a [Prop], namely the goal to provide hints for.
    
  Returns:
    - [message], message containing a hint.
  
  Raises exceptions:
    - [GoalHintError], if no hint is available for [g].
*)
Ltac2 goal_to_hint (g:constr) :=
  (* The order matters. If the ∀ case is above the ⇒, then implications will fire the ∀ case instead.*)
  lazy_match! g with
    | ?a -> ?b  => 
      let sort_a := get_value_of_hyp a in
      match check_constr_equal sort_a constr:(Prop) with
        | true  => create_implication_message a
        | false => create_function_message a
      end
    | forall v:?v_type, _ => create_forall_message v_type
    | exists v:?v_type, _ => create_exists_message v_type
    | _ /\ _ => of_string
"The goal is to show a conjunction (∧).
Show both statements, use ‘We show both statements.’"
    | _ \/ _ => of_string
"The goal is to show a disjunction (∨).
Show one of the statements, use ‘It suffices to show that (...).’ with the dots replaced with the statement you decide to show."
    | Case.Wrapper _ _                => create_goal_wrapped_message ()
    | NaturalInduction.Base.Wrapper _ => create_goal_wrapped_message ()
    | NaturalInduction.Step.Wrapper _ => create_goal_wrapped_message ()
    | StateGoal.Wrapper _             => create_goal_wrapped_message ()
    | ByContradiction.Wrapper _ _     => create_goal_wrapped_message ()
    | not ?g => create_not_message g
    | False  => create_goal_wrapped_message ()
    | _ => 
      match Control.case (solvable_by_core_auto) with
        | Val _ => of_string "The goal can be shown immediately, use ‘We conclude that (...).’."
        | Err exn => Control.zero Inner
      end
  end.

(**
  Print a hint indicating a potential step to proving the current goal (if the goal is a ∀, ⇒ or ∃ proposition).
  When no hint is available, print "No hint available".

  Arguments:
    - [g: constr option], optional goal to generate hint for. If [None] is given, then uses currently active goal.
*)
Ltac2 print_goal_hint (g: constr option) :=
  let g' := 
    match g with
      | None => Control.goal ()
      | Some y => y
    end
  in let f () := goal_to_hint g' in
  match Control.case f with
    | Val mess => 
      match mess with
        | (mess, _) => print mess
      end
    | Err exn => print (of_string "No hint available for this goal.")
  end.

(** * Help tactic
    Tries to give a hint how to proceed proving the current goal.
*)
Ltac2 Notation "Help" := print_goal_hint None.