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

Require Import Notations.Sets.
Open Scope subset_scope.

Require Import Waterprove.

Local Ltac2 goal_impl_msg (premise: constr) :=
  concat_list [of_string "The goal is to show an implication (⇒).
Assume the premise "; of_constr premise; of_string ", use
    Assume that (...)."].

Local Ltac2 goal_func_msg (var_type: constr) :=
  concat_list [of_string "The goal is to construct a map (⇒).
Introduce an arbitrary variable of type "; of_constr var_type; of_string ", use
    Take ... : (...)."].

Local Ltac2 goal_forall_msg (var_type: constr) :=
  concat_list [of_string "The goal is to show a ‘for all’-statement (∀).
Introduce an arbitrary variable of type "; of_constr var_type; of_string ", use
    Take ... : (...)."].

Local Ltac2 goal_exists_msg (var_type: constr) :=
  concat_list [of_string "The goal is to show a ‘there exists’-statement (∃).
Choose a specific variable of type "; of_constr var_type; of_string ", use
    Choose ... := (...)."].

Local Ltac2 goal_forall_el_msg (var_type: constr) :=
  concat_list [of_string "The goal is to show a ‘for all’-statement (∀).
Introduce an arbitrary variable in "; of_constr var_type; of_string ", use
    Take ... ∈ (...)."].

Local Ltac2 goal_forall_gt_msg (y: constr) :=
  concat_list [of_string "The goal is to show a ‘for all’-statement (∀).
Introduce an arbitrary variable strictly larger than "; of_constr y; of_string ", use
    Take ... > (...)."].

Local Ltac2 goal_forall_ge_msg (y: constr) :=
  concat_list [of_string "The goal is to show a ‘for all’-statement (∀).
Introduce an arbitrary variable larger than or equal to "; of_constr y; of_string ", use
    Take ... ≥ (...)."].

Local Ltac2 goal_forall_lt_msg (y: constr) :=
  concat_list [of_string "The goal is to show a ‘for all’-statement (∀).
Introduce an arbitrary variable strictly less than "; of_constr y; of_string ", use
    Take ... < (...)."].

Local Ltac2 goal_forall_le_msg (y: constr) :=
  concat_list [of_string "The goal is to show a ‘for all’-statement (∀).
Introduce an arbitrary variable less than or equal to "; of_constr y; of_string ", use
    Take ... ≤ (...)."].

Local Ltac2 goal_exists_el_msg (var_type: constr) :=
  concat_list [of_string "The goal is to show a ‘there exists’-statement (∃).
Choose a specific variable in "; of_constr var_type; of_string ", use
    Choose ... := (...)."].

Local Ltac2 goal_exists_gt_msg (y: constr) :=
  concat_list [of_string "The goal is to show a ‘there exists’-statement (∃).
Choose a specific variable strictly larger than "; of_constr y; of_string ", use
    Choose ... := (...)."].

Local Ltac2 goal_exists_ge_msg (y: constr) :=
  concat_list [of_string "The goal is to show a ‘there exists’-statement (∃).
Choose a specific variable larger than or equal to "; of_constr y; of_string ", use
    Choose ... := (...)."].

Local Ltac2 goal_exists_lt_msg (y: constr) :=
  concat_list [of_string "The goal is to show a ‘there exists’-statement (∃).
Choose a specific variable strictly less than "; of_constr y; of_string ", use
    Choose ... := (...)."].

Local Ltac2 goal_exists_le_msg (y: constr) :=
  concat_list [of_string "The goal is to show a ‘there exists’-statement (∃).
Choose a specific variable less than or equal to "; of_constr y; of_string ", use
    Choose ... := (...)."].

Local Ltac2 goal_and_msg () := of_string
  "The goal is to show a conjunction (∧).
Show both statements, use
    We show both statements.".

Local Ltac2 goal_or_msg () := of_string
"The goal is to show a disjunction (∨).
It suffices to show one of the statements, use
    It suffices to show that (...).".

Local Ltac2 goal_neg_msg (negated_type : constr) :=
  concat_list [of_string "The goal is to show a negation (¬).
Assume that the negated expression "; of_constr negated_type; of_string ", use
    Assume that (...)."].

Local Ltac2 goal_directly () := of_string
  "The goal can be shown immediately, use
    We conclude that (...).".

Local Ltac2 goal_no_hint ():= of_string
  "No direct hint available.
Does the goal contain a definition that can be expanded?".


(**
  Auxilliary tactic that checks if goal can be shown with automation
*)
Local Ltac2 solvable_by_core_auto () :=
  let temp_id := Fresh.in_goal @temp in
  let goal := Control.goal () in
  assert $goal as $temp_id;
  Control.focus 1 1 (fun () => waterprove 5 true Main);
  clear $temp_id.


Local Ltac2 need_to_follow_advice () : bool :=
  let gl := Control.goal () in
  lazy_match! gl with
  | Case.Wrapper _ _                => true
  | NaturalInduction.Base.Wrapper _ => true
  | NaturalInduction.Step.Wrapper _ => true
  | StateGoal.Wrapper _             => true
  | StateHyp.Wrapper _ _ _          => true
  | ByContradiction.Wrapper _ _     => true
  | False                           => true
  | _ => false
  end.

Local Ltac2 goal_hint () : message :=
  let gl := Control.goal () in
  lazy_match! gl with
  | ?a -> ?b  =>
    let sort_a := get_value_of_hyp a in
    match check_constr_equal sort_a constr:(Prop) with
      | true            => goal_impl_msg a
      | false           => goal_func_msg a
    end
  | ∀ _ ∈ conv ?v_type, _  => goal_forall_el_msg v_type
  | ∀ _ ∈ ?v_type, _  => goal_forall_el_msg v_type
  | ∀ _ > ?y, _          => goal_forall_gt_msg y
  | ∀ _ ≥ ?y, _          => goal_forall_ge_msg y
  | ∀ _ < ?y, _          => goal_forall_lt_msg y
  | ∀ _ ≤ ?y, _          => goal_forall_le_msg y
  | ∃ _ ∈ conv ?v_type, _    => goal_exists_el_msg v_type
  | ∃ _ ∈ ?v_type, _    => goal_exists_el_msg v_type
  | ∃ _ > ?y, _         => goal_exists_gt_msg y
  | ∃ _ ≥ ?y, _         => goal_exists_ge_msg y
  | ∃ _ < ?y, _         => goal_exists_lt_msg y
  | ∃ _ ≤ ?y, _         => goal_exists_le_msg y
  | forall v:?v_type, _ => goal_forall_msg v_type
  | exists v:?v_type, _ => goal_exists_msg v_type
  | _ /\ _              => goal_and_msg ()
  | _ \/ _              => goal_or_msg ()
  | not ?g              => goal_neg_msg g
  | _                   => goal_no_hint ()
  end.

Local Ltac2 forall_filter (x : constr) : bool :=
  lazy_match! x with
  | ?a -> ?b     => false
  | ∀ _ ∈ _, _   => true
  | ∀ _ > _, _   => true
  | ∀ _ ≥ _, _   => true
  | forall _, _  => true
  | _            => false
  end.

Local Ltac2 exists_filter (x : constr) : bool :=
  lazy_match! x with
  | exists _, _  => true
  | ∃ _ ∈ _, _   => true
  | ∃ _ > _, _   => true
  | ∃ _ ≥ _, _   => true
  | _            => false
  end.

Local Ltac2 is_empty (ls : 'a list) :=
  match ls with
  | _::_ => false
  | []   => true
  end.


Ltac2 print_hints () :=

  (* If advice is given in proof window, suggest to follow that, nothing else. *)
  if (need_to_follow_advice ())
    then (print (of_string "Follow the advice in the goal window."))

    else
      (* Then if proof can be shown automatically, suggest that, nothing else. *)
      match Control.case (solvable_by_core_auto) with
      | Val _           => print (goal_directly ())
      | Err exn         =>

        (* Suggest hint to solve goal *)
        print (goal_hint ());

        (* Collect forall- and exists-statements *)
        let hyps := List.map (fun (i, x, t) => t) (Control.hyps ()) in
        let forall_hyps := List.filter (forall_filter) hyps in
        let exists_hyps := List.filter (exists_filter) hyps in

        (* Print how to use forall-statements. *)
        if (is_empty forall_hyps)
          then ()
          else (
            print(of_string "To use one of the ‘for all’-statements (∀)");
            List.fold_left (fun _ h => print (concat (of_string "    ") (of_constr h))) forall_hyps ();
            print(of_string "use");
            print(of_string "    Use ... := (...) in (...).")
          );

        (* Print how to use exists statements. *)
        if (is_empty exists_hyps)
          then ()
          else (
            print(of_string "To use one of the ‘there exists’-statements (∃)");
            List.fold_left (fun _ h => print (concat (of_string "    ") (of_constr h))) exists_hyps ();
            print(of_string "use");
            print(of_string "    Obtain ... according to (...).")
          )
      end.


(** * Help tactic
    Tries to give a hint how to proceed proving the current goal.
*)
Ltac2 Notation "Help" := print_hints ().





Module HelpNewHyp.

(** Given a forall- or exists-statement, prints suggestion how to use it. *)

Ltac2 suggest_how_to_use (x : constr) (label : ident option) :=
  if Bool.neg (get_print_hypothesis_flag ()) then ()
  else
  let msg_label :=
    match label with
    | None   => of_string "..."
    | Some i => of_ident i
    end
  in
  let print_forall_msg () :=
    print (concat_list [
        of_string "To use "; of_constr x; of_string ", use"]);
      print (concat_list [
        of_string "    Use ... := (...) in ("; msg_label; of_string ")."]) in
  let print_exists_msg () :=
    print (concat_list [
        of_string "To use "; of_constr x; of_string ", use"]);
      print (of_string "    Obtain such a ... .") in
  lazy_match! x with
  | ?a -> ?b => ()
  | forall _, _ => print_forall_msg ()
  | ∀ _ ∈ _ , _ => print_forall_msg ()
  | ∀ _ > _ , _ => print_forall_msg ()
  | ∀ _ ≥ _, _ => print_forall_msg ()
  | ∀ _ < _ , _ => print_forall_msg ()
  | ∀ _ ≤ _, _ => print_forall_msg ()
  | exists _, _ => print_exists_msg ()
  | ∃ _ ∈ _, _ => print_exists_msg ()
  | ∃ _ > _, _ => print_exists_msg ()
  | ∃ _ ≥ _, _ => print_exists_msg ()
  | ∀ _ < _ , _ => print_forall_msg ()
  | ∀ _ ≤ _, _ => print_forall_msg ()
  | _ => ()
  end.

(** Given a forall- or exists-statement, prints suggestion how to use it,
  after statement is proven.

  (for use in 'We claim that ...'-tactic.)
*)

Ltac2 suggest_how_to_use_after_proof (x : constr) (label : ident option) :=
  if Bool.neg (get_print_hypothesis_flag ()) then ()
  else
  let msg_label :=
    match label with
    | None   => of_string "..."
    | Some i => of_ident i
    end
  in
  let print_forall_msg () :=
    print (concat_list [
        of_string "After proving "; of_constr x; of_string ", use it with"]);
      print (concat_list [
        of_string "    Use ... := (...) in ("; msg_label; of_string ")."]) in
  let print_exists_msg () :=
    print (concat_list [
        of_string "After proving "; of_constr x; of_string ", use it with"]);
      print (of_string "    Obtain such a ... .") in
  lazy_match! x with
  | ?a -> ?b => ()
  | forall _, _ => print_forall_msg ()
  | ∀ _ ∈ _, _ => print_forall_msg ()
  | ∀ _ > _, _ => print_forall_msg ()
  | ∀ _ ≥ _, _ => print_forall_msg ()
  | exists _, _ => print_exists_msg ()
  | ∃ _ ∈ _, _ => print_exists_msg ()
  | ∃ _ > _, _ => print_exists_msg ()
  | ∃ _ ≥ _, _ => print_exists_msg ()
  | _ => ()
  end.

End HelpNewHyp.

Close Scope subset_scope.
