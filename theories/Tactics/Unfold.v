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
Require Import Waterproof.Tactics.ItSuffices.
Require Import Waterproof.Tactics.ItHolds.
Local Ltac2 concat_list (ls : message list) : message :=
  List.fold_right concat ls (of_string "").

Require Import Util.Goals.
Require Import Util.MessagesToUser.

Ltac2 Type unfold_action := [
  | Unfold (reference)
  | Apply (constr)
  | Rewrite (constr)
].

Ltac2 @ external extract_def_ffi : string -> reference option := "rocq-runtime.plugins.coq-waterproof" "extract_def_external".
Ltac2 @ external find_unfold_actions_ffi : string -> unfold_action list := "rocq-runtime.plugins.coq-waterproof" "find_unfold_actions_external".

Local Ltac2 _is_empty (ls : 'a list) :=
  match ls with
  | _::_ => false
  | []   => true
  end.

Ltac2 Type exn ::=  [ Inner ].

(**
This module provides a framework for unfolding definitions and alternative characterizations.

Please have a look at
the test file [tests/tactics/Unfold.v]

and at the bottom of the file
[Libs/Analysis/SupAndInf.v]

for the syntax for adding new definitions and alternative characterizations.

For using alternative characterizations, one can use

[Hint Resolve -> ... : wp_alt_chars.]
[Hint Resolve <- ... : wp_alt_chars.]

to add both directions of the equivalence to the proper automation database.

*)

(**
TODO / Note:

Some alternative characterizations will need to be added to a special
wp_alt_chars database, especially if they involve expressions that would
otherwise be shielded by the automation.
*)

(**
What follows are two methods to deal with alternative characterizations.
The second method uses rewriting and when combined with propositional extensionality,
can give significantly strong statmemnts than the first. Reasons why one might prefer
the first over the second:

- If one doesn't want to take too large steps
- If the automation cannot handle the rewriting used in the stronger tactic.
*)

(**
  Helper tactic that can be used as an unfold method in
  [unfold_in_all] below. This version can be used for simple reformulation
  of alternative characterizations. It will likely only work
  if the constant to unfold is the head constant.

  Arguments:
  - [alt_char : constr] An alternative characterization for the concept
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

  Arguments:
  - [equality : constr] An equality with which to rewrite the concept
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

Ltac2 unfold_method_for_action (ua : unfold_action) (stmt : constr) : constr :=
  match ua with
  | Unfold r => eval unfold $r in $stmt
  | Apply equiv => apply_in_constr equiv stmt
  | Rewrite eq => tactic_in_constr eq stmt
  end.

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

Local Ltac2 Type exn ::= [Succeeded].

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
            match Control.case (fun () => It suffices to show that $unfolded_goal; Control.zero Succeeded) with
            | Err Succeeded => (print_tactic (concat_list [of_string "It suffices to show that ";
                                of_constr unfolded_goal; of_string "."]))
            | _ => warn (concat_list [of_string "The following suggestion will likely not work,";
            of_string " (this is probably caused by a misalignment in the automation for";
            of_string " unfolding statements. Please notify your teacher or the Waterproof developers):"; fnl(); of_string "It suffices to show that ";
                                of_constr unfolded_goal; of_string "."])
            end
        else ();

      (* Print unfolded hypotheses *)
      if (Bool.neg (_is_empty only_unfolded_hyps))
        then
          let it_holds_msg := fun (x : constr) => concat_list
            [of_string "It holds that "; of_constr x; of_string "."] in
          let test_and_print unfolded_h :=
            match Control.case (fun () => It holds that $unfolded_h; Control.zero Succeeded) with
            | Err Succeeded => print_tactic (it_holds_msg unfolded_h)
            | _ => warn (concat_list [of_string "The following suggestion will likely not work,";
            of_string " (this is probably caused by a misalignment in the automation for";
            of_string " unfolding statements. Please notify your teacher or the Waterproof developers):"; fnl(); it_holds_msg unfolded_h])
            end in
          if definitional then
            (List.iter (fun unfolded_h => print_tactic (it_holds_msg unfolded_h))) only_unfolded_hyps
          else
            (List.iter test_and_print only_unfolded_hyps)
        else ()

    else
      (* Print no statements with definition *)
      if definitional then
        (match def_name with
        | None => info_notice (of_string "Definition does not appear in any statement.")
        | Some def_name => info_notice (concat_list
            [of_string "'"; of_string def_name; of_string "'";
              of_string " does not appear in any statement."])
        end) else ();

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

(**
  Attempts to unfold definition(s) in statements according to unfold actions that have
  been pre-stored in a database.

  Here are some examples of syntax for adding unfold actions to the database.
  For more examples, see [tests/tactics/Unfold.v].

  [Waterproof Register Unfold "converges" "to" converges_to.
  Waterproof Register Unfold Apply "infimum" is_infimum ; (alt_char_inf).
  Waterproof Register Unfold Rewrite "powerRZ" powerRZ ; (powerRZ_Rpower).]
*)
Ltac2 Notation "Unfold" "the" "definition" "of" _x(tactic) :=
  let definitional_for_action (ua : unfold_action) := match ua with
  | Unfold _ => true
  | Apply _ => false
  | Rewrite _ => false
  end in
  List.iter (fun z =>
      wp_unfold (unfold_method_for_action z) None false (definitional_for_action z) None)
    (find_unfold_actions_ffi _x);
  throw (of_string "Remove this line in the final version of your proof.").

(* For now, include optional tail to keep compatible with tactic called by Waterproof editor. *)
Ltac2 Notation "_internal_" "Expand" "the" "definition" "of" targets(list1(seq(reference, occurrences), ",")) :=
  wp_unfold (eval_unfold targets) None false true None.
