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

Require Import Chains.Inequalities.
Require Import Util.Goals.
Require Import Util.Init.
Require Import Util.Since.
Require Import Waterprove.
Require Import MessagesToUser.

Local Ltac2 concat_list (ls : message list) : message :=
  List.fold_right concat (of_string "") ls.

Ltac2 warn_equivalent_goal_given () :=
  warn (of_string 
"The statement you provided does not exactly correspond to what you need to show. 
This can make your proof less readable."
  ).

Ltac2 wrong_goal_msg (wrong_goal : constr) :=
  concat_list 
    [of_constr wrong_goal; of_string " does not correspond to what you need to show."].

(**
  Check if [target] is judgementally (i.e. by rewriting definitions) equal to the goal.

  Arguments:
    - [target:constr], expression to compare to goal.

  Returns:
    - [bool]: indicates if [target] is judgementally equal to the goal under focus.
*)
Local Ltac2 target_equals_goal_judgementally (target : constr) :=
  let target := eval cbv in $target in
  let real_goal := Control.goal () in
  let real_goal := eval cbv in $real_goal in 
  Constr.equal target real_goal.


(**
  Check if stated goal is what needs to be proven judgementally.
  If so changes current goal into stated goal.
  Uses global or weak global statement inequality chains of to compare
  these to the current goal.  

  Arguments:
    - [sttd_goal: constr], stated goal, the expression that should equal the goal under focus.
    
  Raises fatal exceptions:
    - If [sttd_goal] is not equivalent to the actual goal under focus, even after rewriting.
*)


Local Ltac2 guarantee_stated_goal_matches (sttd_goal : constr) :=
  (* Check if stated goal exactly matches current goal. *)
  match Constr.equal sttd_goal (Control.goal ()) with
  | true => ()
  | false => 
    (* If not, do some additional checks. *)
    (* For inequality chains, consider the global statement. *)
    lazy_match! sttd_goal with
    | total_statement ?u =>
      (* Check if global statement matches judgementally. *)
      let glob_statement := constr:(global_statement $u) in
      match target_equals_goal_judgementally glob_statement with
      | true => ()
      | false =>
        (* If not, try weak global statement. *)
        let weak_glob_statement := constr:(weak_global_statement $u) in
        match target_equals_goal_judgementally weak_glob_statement with
        | true => ()
        | false => throw (wrong_goal_msg sttd_goal)
        end
      end;
      (* Convert current goal to the given inequality chain.*)
      enough $sttd_goal by (waterprove 5 false Main)
    (* For the rest, just check for judgemental equality. *)
    | _ => 
      match target_equals_goal_judgementally sttd_goal with
      | true => warn_equivalent_goal_given (); change $sttd_goal  
      | false => throw (wrong_goal_msg sttd_goal)
      end
    end
  end.

(** Attempts to solve current goal. *)
Local Ltac2 conclude () := 
  let err_msg (g : constr) := concat_list
    [of_string "Could not verify that "; of_constr g; of_string "."] 
  in
  match Control.case (fun () => waterprove 5 true Main) with
  | Val _ => ()
  | Err (FailedToProve g) => throw (err_msg g)
  | Err exn => Control.zero exn
  end.

(** Attempts to solve current goal using additional lemma which has to be used. *)
Local Ltac2 core_conclude_by (xtr_lemma : constr) :=
  let err_msg (g : constr) := concat_list
    [of_string "Could not verify that "; of_constr g; of_string "."] 
  in
  match Control.case (fun () =>
    rwaterprove 5 true Main xtr_lemma)
  with
  | Val _ => ()
  | Err (FailedToProve g) => throw (err_msg g)
  | Err exn => Control.zero exn (* includes FailedToUse error *)
  end.

(** Adaptation of [core_conclude_by] that turns the [FailedToUse] errors 
  which might be thrown into user readable errors. *)
Local Ltac2 conclude_by (xtr_lemma : constr) :=
  wrapper_core_by_tactic core_conclude_by xtr_lemma.

(** Adaptation of [core_conclude_by] that allows user to use mathematical statements themselves
  instead of references to them as extra information for the automation system.
  Uses the code in [Since.v]. *)
Local Ltac2 conclude_since (xtr_claim : constr) :=
  since_framework core_conclude_by xtr_claim.



(**
  Removes a [StateGoal.Wrapper] wrapper from the goal.
    
  Arguments: None
    
  Does: 
    - Removes the wrapper [StateGoal.Wrapper G].
*)
Local Ltac2 unwrap_state_goal_no_check () :=
  lazy_match! goal with
    | [|- StateGoal.Wrapper _] => apply StateGoal.wrap
    | [|- _] => ()
  end.


(**
  Finish proving a goal using automation.

  Arguments:
    - [target_goal: constr], expression that should equal the goal under focus.

  Raises exceptions:
    - [AutomationFailure], if [waterprove] fails the prove the goal (i.e. the goal is too difficult, or does not hold).
    - [ConcludeError], if [target_goal] is not equivalent to the actual goal under focus, even after rewriting.
*)
Ltac2 Notation "We" "conclude" tht(opt("that")) target_goal(constr) := 
  unwrap_state_goal_no_check ();
  panic_if_goal_wrapped ();
  guarantee_stated_goal_matches target_goal;
  conclude ().

(**
  Alternative notation for [We conclude that ...].
*)
Ltac2 Notation "It" "follows" tht(opt("that")) target_goal(constr) :=      
  unwrap_state_goal_no_check ();
  panic_if_goal_wrapped ();
  guarantee_stated_goal_matches target_goal;
  conclude ().

(**
  Finish proving a goal using automation.

  Arguments:
    - [target_goal: constr], expression that should equal the goal under focus.
    - [xtr_lemma: constr], lemma that can be and has to be used for proof of [target_goal].

  Raises exceptions:
    - [AutomationFailure], if [waterprove] fails the prove the goal (i.e. the goal is too difficult, or does not hold).
    - [ConcludeError], if [target_goal] is not equivalent to the actual goal under focus, even after rewriting.
*)
Ltac2 Notation "By" xtr_lemma(constr) "we" "conclude" tht(opt("that")) target_goal(constr) :=
  unwrap_state_goal_no_check ();
  panic_if_goal_wrapped ();
  guarantee_stated_goal_matches target_goal;
  conclude_by xtr_lemma.

Ltac2 Notation "Since" xtr_claim(constr) "we" "conclude" tht(opt("that")) target_goal(constr) :=
  unwrap_state_goal_no_check ();
  panic_if_goal_wrapped ();
  guarantee_stated_goal_matches target_goal;
  conclude_since xtr_claim.
