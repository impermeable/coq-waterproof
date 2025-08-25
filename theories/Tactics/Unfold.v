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

  Raises fatal exceptions:
    - [always/none] depending on value of [throw_error].
*)

Ltac2 unfold_in_all (unfold_method: constr -> constr)
  (def_name : string option) (throw_error : bool) :=


  let goal := Control.goal () in
  let unfolded_goal := unfold_method goal in
  let did_unfold_goal := Bool.neg (Constr.equal unfolded_goal goal) in

  let hyps := List.map (fun (i, def, t) => t) (Control.hyps ()) in
  let unfolded_hyps := List.map unfold_method hyps in
  let only_unfolded_hyps :=
    List.map (fun (uh, h) => uh) (
      List.filter_out (fun (uh, h) => Constr.equal uh h) (
        List.combine unfolded_hyps hyps
      )
    ) in

  (* Print output *)
  if (Bool.or did_unfold_goal (Bool.neg (_is_empty only_unfolded_hyps)))
    then
      (* Print initial statement *)
      info_notice (of_string "Expanded definition in statements where applicable.");
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
          print_tactic (concat_list [of_string "We need to show that ";
            of_constr unfolded_goal; of_string "."])
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
  (def_name : string option) (throw_error : bool) (x : constr option):=
  panic_if_goal_wrapped ();
  unfold_in_all unfold_method def_name throw_error.

(* TODO: Refactor unfold system to be more maintainable *)

(* Tactic notation for unfolding generic Gallina terms, not notations.
  For an example of how to used [unfold_in_statement] to unfold notations,
  see [tests/tactics/Unfold.v] *)
Ltac2 Notation "Expand" "the" "definition" "of" targets(list1(seq(reference, occurrences), ",")) :=

  wp_unfold (eval_unfold targets) None true None.

(* For now, include optional tail to keep compatible with tactic called by Waterproof editor. *)
Ltac2 Notation "_internal_" "Expand" "the" "definition" "of" targets(list1(seq(reference, occurrences), ",")) :=
  wp_unfold (eval_unfold targets) None false None.
