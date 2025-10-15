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
Require Import Ltac2.Std.
Require Import Ltac2.Message.
Local Ltac2 concat_list (ls : message list) : message :=
  List.fold_right concat ls (of_string "").

Require Import Util.Goals.
Require Import Util.MessagesToUser.

Local Ltac2 _is_empty (ls : 'a list) :=
  match ls with
  | _::_ => false
  | []   => true
  end.

Ltac2 Type exn ::=  [ Inner ].

(**
  Helper tactic that can be used as an unfold method in
  [unfold_in_all] below. This version can be used for simple reformulation
  of alternative characterizations. It will likely only work
  if the constant to unfold is the head constant.

  Note: as of now, it is important that this lemma is available
  in the automation databases that are used! This is not
  explicitly checked here or below.
  TODO: See if we want to add a check

  Arguments:
  - [alt_char : constr] An implication implying the concept
    to unfold
  - [x : constr] The expression in which the concept should
    be unfolded
*)
Ltac2 apply_in_constr (alt_char : constr) (x : constr) : constr :=
  let h := Fresh.fresh (Fresh.Free.of_goal () ) @__wp__h in
  assert (False -> $x) as $h;
  let return_term : constr :=
    (Control.focus 1 1 (fun () =>
      let h1 := Fresh.fresh (Fresh.Free.of_goal () ) @__wp__h in
      intro $h1;
      try (apply $alt_char);
      let rewritten_term := Control.goal() in
      let h2 := Control.hyp h1 in
      destruct $h2;
      exact I;
      rewritten_term)
    ) in
  clear $h;
  return_term.

(**
  Helper tactic that can be used as an unfold method in
  [unfold_in_all] below. When combined with propositional
  extensionality, this can give a slightly more advanced
  reformulation using an alternative characterization.
  It will likely work in more cases than [apply_in_constr].

  Note: as of now, if one wants to use this way of unfolding,
  it is important that this rewrite action is available
  in the automation databases that are used! This is not
  explicitly checked here or below.
  TODO: See if we want to add a check

  Arguments:
  - [alt_char : constr] An implication implying the concept
    to unfold
  - [x : constr] The expression in which the concept should
    be unfolded
*)
Ltac2 tactic_in_constr (equality : constr) (x : constr) : constr :=
  let h := Fresh.fresh (Fresh.Free.of_goal () ) @__wp__h in
  assert ($x -> True) as $h;
  let return_term : constr :=
    (Control.focus 1 1 (fun () =>
      try (setoid_rewrite $equality);
      let rewritten_term :=
      match! goal with
      | [|- ?c -> True ] => c
      | [|- _] => throw (Message.of_string "Unexpected error in tactic_in_constr. Please report."); constr:(False)
      end in
      intro;
      exact I;
      rewritten_term)
    ) in
  clear $h;
  return_term.

(**
  Attempts to unfold definition(s) in every statement according to specified method.
  If succesful it prints a list of suitable tactics
  that can be used to incorporate the unfolded statements into the user's proof script.
    E.g. if the defition was unfolded in the proof goal, the list will include
    'We need to show that ([statement with unfolded definiton])'.

  Arguments:
    - [unfold method: constr -> constr], method to be used for unfolding
        unfolding is deemed to be succesful if [unfold_method statement] =\= [statement]
    - [def_name: string], optional string used for error message when unfolding
        is unsuccesful
    - [throw_error : bool], whether the tactic should throw an error which suggests
        user to remove this tactic in final version of the proof.
    - [definitional : bool], whether the unfolded version is definitionally equal to the original (as opposed to an alternative characterization)

  Raises fatal exceptions:
    - [always/none] depending on value of [throw_error].
*)

Ltac2 unfold_in_all (unfold_method: constr -> constr)
  (def_name : string option) (throw_error : bool) (definitional : bool) :=
  let goal := Control.goal () in
  let unfolded_goal := unfold_method goal in
  let did_unfold_goal := Bool.neg (Constr.equal unfolded_goal goal) in
  let hyps := List.map (fun (_, _, t) => t) (Control.hyps ()) in
  let unfolded_hyps := List.map unfold_method hyps in
  let only_unfolded_hyps :=
    List.map (fun (uh, _) => uh) (
      List.filter_out (fun (uh, h) => Constr.equal uh h) (
        List.combine unfolded_hyps hyps
      )
    ) in
  (* Print output *)
  if (Bool.or did_unfold_goal (Bool.neg (_is_empty only_unfolded_hyps)))
    then
      (* Print initial statement *)
      if definitional then
        (info_notice (of_string "Expanded definition in statements where applicable."))
      else
        (info_notice (of_string "Applied alternative characterizations in statements where applicable."));
      let total_messages := Int.add
        (if did_unfold_goal then 1 else 0)
        (List.length only_unfolded_hyps) in

      let print_tactic :=
        if (Int.lt 1 total_messages) then
          fun m => insert_msg (to_string m) (to_string (concat m (of_string "${}")))
        else
          fun m => replace_msg (to_string m) (to_string (concat m (of_string "${}")))
        in

      (* Print unfolded goal *)
      if did_unfold_goal
        then
          if definitional then
            (print_tactic (concat_list [of_string "We need to show that ";
              of_constr unfolded_goal; of_string "."]))
          else
            (print_tactic (concat_list [of_string "It suffices to show that ";
              of_constr unfolded_goal; of_string "."]))
        else ();

      (* Print unfolded hypotheses *)
      if (Bool.neg (_is_empty only_unfolded_hyps))
        then
          let it_holds_msg := fun (x : constr) => concat_list
            [of_string "It holds that "; of_constr x; of_string "."] in
          List.iter (fun unfolded_h => print_tactic (it_holds_msg unfolded_h))
            only_unfolded_hyps
        else ()

    else
      (* Print no statements with definition *)
      match def_name with
      | None => info_notice (of_string "Definition does not appear in any statement.")
      | Some def_name => info_notice (concat_list
          [of_string "'"; of_string def_name; of_string "'";
            of_string " does not appear in any statement."])
      end;

  (* Throw error if required *)
  if throw_error
    then throw (of_string "Remove this line in the final version of your proof.")
    else ().

(**
  Either attempts to unfold definition(s) in every statement according to specified method, or
  attempts to unfold definition(s) in the provided statement.
  If succesful it prints a list of suitable tactics
  that can be used to incorporate the unfolded statements into the user's proof script.
    E.g. if the defition was unfolded in the proof goal, the list will include
    'We need to show that ([statement with unfolded definiton])'.

  Arguments:
    - [unfold method: constr -> constr], method to be used for unfolding
        unfolding is deemed to be succesful if [unfold_method statement] =\= [statement]
    - [def_name: string], optional string used for error message when unfolding
        is unsuccesful
    - [throw_error : bool], whether the tactic should throw an error which suggests
        user to remove this tactic in final version of the proof.
    - [x : constr option], unused, kept for compatibility.

  Raises fatal exceptions:
    - [always/none] depending on value of [throw_error].
*)
Ltac2 wp_unfold (unfold_method: constr -> constr)
  (def_name : string option) (throw_error : bool)
  (judgmental : bool) (_ : constr option) :=
  panic_if_goal_wrapped ();
  unfold_in_all unfold_method def_name throw_error judgmental.

(* TODO: Refactor unfold system to be more maintainable *)

(* Tactic notation for unfolding generic Gallina terms, not notations.
  For an example of how to used [unfold_in_statement] to unfold notations,
  see [tests/tactics/Unfold.v] *)
Ltac2 Notation "Expand" "the" "definition" "of" targets(list1(seq(reference, occurrences), ",")) :=

  wp_unfold (eval_unfold targets) None true true None.

(* For now, include optional tail to keep compatible with tactic called by Waterproof editor. *)
Ltac2 Notation "_internal_" "Expand" "the" "definition" "of" targets(list1(seq(reference, occurrences), ",")) :=
  wp_unfold (eval_unfold targets) None false true None.
