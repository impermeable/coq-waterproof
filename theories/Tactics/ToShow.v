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

Require Import Util.Constr.
Require Import Util.Goals.
Require Import Tactics.Unfold.
Require Import Waterprove.

(* Require Import Automation. *)

Ltac2 Type exn ::= [ GoalCheckError(message) | AutomationFailure(message) ].

Require Import Ltac2.Message.

(**
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
      match check_constr_equal g t with
        | true => ()
                  (* print (concat (of_string "The goal is indeed: ") (of_constr t))*)
        | false => Control.zero (GoalCheckError (of_string "Wrong goal specified."))
      end
  end.


Local Ltac2 concat_list (ls : message list) : message :=
  List.fold_right concat (of_string "") ls.

(** Check if proposed statement is equivalent to current goal;
  if so, replace the goal by the proposed statement.  *)
Local Ltac2 change_to_equivalent_goal (new_g : constr) :=
  lazy_match! goal with
  | [ |- ?g] =>
    let err_msg := concat_list [
        (of_string "Could not verify that "); (of_constr new_g);
        (of_string " is equivalent to "); (of_constr g); (of_string ".")] in
    let temp_id := Fresh.in_goal @_temp in
    let solver () := waterprove 5 false [] Main in
    match Control.case (fun () => 
      assert ($g -> $new_g) as $temp_id by (solver ()))
    with
    | Err exn => Control.zero (AutomationFailure err_msg)
    | Val _ => 
      clear $temp_id;
      match Control.case (fun () =>
        enough $new_g by (solver ()))
      with
      | Err exn => Control.zero (AutomationFailure err_msg)
      | Val _ => ()
      end
    end
  end.

(** Check if from specified lemma it follows that 
  proposed statement is equivalent to current goal;
  if so, replace the goal by the proposed statement.
    *)
Local Ltac2 change_to_equivalent_goal_by (new_g : constr) (xtr_lemma : constr) :=
  lazy_match! goal with
  | [ |- ?g] =>
    let err_msg := concat_list [
        (of_string "Could not verify that "); (of_constr new_g);
        (of_string " is equivalent to "); (of_constr g); (of_string ".")] in
    let temp_id := Fresh.in_goal @_temp in
    (* Extra lemma has to be used, either to prove g -> new_g or the converse. *)
    match Control.case (fun () =>
      assert ($g -> $new_g) as $temp_id by
        (rwaterprove 5 false [fun () => xtr_lemma] Main [xtr_lemma] []))
    with
    | Val _ =>
      (* g -> new_g shown using extra lemma, converse can be shown without restriction *)
      clear $temp_id;
      match Control.case (fun () =>
        enough $new_g by 
          (waterprove 5 false [fun () => xtr_lemma] Main))
      with
      | Val _ => ()
      | Err exn => Control.zero (AutomationFailure err_msg)
      end
    | Err exn =>
      (* failed, but could be because of restriction use extra lemma *)
      match Control.case (fun () =>
        assert ($g -> $new_g) as $temp_id by
        (waterprove 5 false [] Main))
      with
      | Err exn => Control.zero (AutomationFailure err_msg)
      | Val _ =>
        (* g -> new_g shown without extra lemma, has to be used in proof converse *)
        clear $temp_id;
        match Control.case (fun () =>
          enough $new_g by 
            (rwaterprove 5 false [fun () => xtr_lemma] Main [xtr_lemma] []))
        with
        | Err exn => (* failed, if due to restricition, give feedback *)
          (* check if it would work without lemma *)
          match Control.case (fun () =>
            enough $new_g by 
              (waterprove 5 false [] Main))
          with
          | Err exn => Control.zero (AutomationFailure err_msg)
          | Val _ =>
            (* problem is the extra lemma: it is not used for proof equivalence *)
            Control.zero (AutomationFailure ( concat_list 
              [of_string "Could not verify this follows from "; of_constr xtr_lemma;
                of_string "."]))
          end
        | Val _ => ()
        end
      end
    end
  end.


(**
  Attempts to remove the [StateGoal.Wrapper] wrapper from the goal.
    
  Arguments:
    - [t : constr], type matching the wrapped goal.
    
  Does: 
    - Removes the wrapper if the argument matches the wrapped goal, i.e. the goal is of the form [StateGoal.Wrapper t].

  Raises Exceptions:
    - [GoalCheckError], if the argument [t] does not match the wrapped goal.
*)
Local Ltac2 unwrap_state_goal (t : constr) :=
  lazy_match! goal with
    | [|- StateGoal.Wrapper ?g] =>
      match (check_constr_equal g t) with
        | true  => apply StateGoal.wrap
        | false => Control.zero (GoalCheckError (of_string "Wrong goal specified."))
      end
  end.

(**
  1) If the goal is wrapped in [ExpandDef.Goal.Wrapper], attempt to remove the wrapper.
  
  2) Else if the goal is wrapped in [State.Goal.Wrapper], attempt to remove it.
  
  3) Else, check if the type of the goal is convertible to [t], if so, it replaces the goal by t.

  Arguments:
    - [t: constr]
      1,2) type matching the wrapped goal.
      3) any constr to be compared against the goal.

  Does:
    - 1,2) Removes the wrapper if the argument matches the wrapped goal, i.e. the goal is of the form [ExandDef.Goal.Wrapper t] ([StateGoal.Wrapper t] resp.).
    - 3) Prints a confirmation that the goal equals the provided type.
    
  Raises Exceptions:
    - 1) [ExpandDefError], if the argument [t] does not match the wrapped goal.
    - 2) [GoalCheckError], if the argument [t] does not match the wrapped goal.
    - 3) [GoalCheckError], if the goal is not convertible to [t].
*)
Local Ltac2 to_show (t : constr) :=
  lazy_match! goal with
    | [|- ExpandDef.Goal.Wrapper _] => goal_as t; change $t (*[goal_as] is from unfold.v*)
    | [|- StateGoal.Wrapper _] => unwrap_state_goal t; change $t
    | [|- _] => panic_if_goal_wrapped (); change_to_equivalent_goal t
  end.

(*
  Allow different syntax styles:
    - We need to show ...
    - We need to show that ...
    - We need to show : ...
    - We need to show that : ...
    - To show ...
    - To show that ...
    - To show : ...
    - To show that : ...

  Optional string keywords do need to have a name, even though the parser will not populate this name. 
  (That's why it reads "that(opt('that'))" instead of "opt('that')".
*)
Ltac2 Notation "We" "need" "to" "show" that(opt("that")) colon(opt(":")) t(constr) := to_show t.

Ltac2 Notation "To" "show" that(opt("that")) colon(opt(":")) t(constr) := to_show t.

(* Use of additional lemma to show equivalent goal. *)
Ltac2 Notation "By" xtr_lemma(constr) "we" "need" "to" "show" that(opt("that")) colon(opt(":")) eqv_goal(constr) :=
  panic_if_goal_wrapped ();
  change_to_equivalent_goal_by eqv_goal xtr_lemma.