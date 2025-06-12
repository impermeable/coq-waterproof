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
  List.fold_right concat (of_string "") ls.

Require Import Util.Goals.
Require Import Util.MessagesToUser.

Local Ltac2 _is_empty (ls : 'a list) :=
  match ls with
  | _::_ => false
  | []   => true
  end.

Ltac2 Type exn ::=  [ Inner ].

(**
  Attemtps to unfold definition(s) in a statement according to specified method.
  If succesful it also throws a fatal error suggesting the user to replace this
  command by an alternative, suitable tactic with the unfolded statement.
    E.g. if the statement corresponds with the proof goal,
  the user is suggested to use
    'We need to show that ([statement with unfolded definiton])'.

  Arguments:
    - [unfold method: constr -> constr], method to be used for unfolding
        unfolding is deemed to be succesful if [unfold_method statement] =\= [statement]
    - [def_name: string], optional string used for error message when unfolding
        is unsuccesful
    - [statement : constr], term in which definitions are to be unfolded.

  Raises fatal exceptions:
    - always if [throw_error = true], because it indicates that the user needs to
      remove this line from the proof script.
    - none if [throw_error = false].

*)
Ltac2 unfold_in_statement (unfold_method: constr -> constr)
  (def_name : string option) (statement : constr) (throw_error : bool) :=
  let unfolded_statement := unfold_method statement in
  match Constr.equal statement unfolded_statement with
  | false =>
    match! goal with
    | [ |- ?g] =>
      match Constr.equal g statement with
      | false => Control.zero Inner
      | true =>
        print (of_string "Replace line with:");
        let msg (unfolded : constr) := concat_list
          [of_string "We need to show that "; of_constr unfolded; of_string "."] in
        print (msg unfolded_statement)
      end
    | [_ : ?hyp |- _ ] =>
      match Constr.equal hyp statement with
      | false => Control.zero Inner
      | true =>
        print (of_string "Replace line with:");
        let msg (unfolded : constr) := concat_list
          [of_string "It holds that "; of_constr unfolded; of_string "."] in
        print (msg unfolded_statement)
      end
    | [ |- _ ] =>
      print (of_string "Result:");
      let msg (unfolded : constr) := concat_list
      [of_constr unfolded] in
      print (msg unfolded_statement)
    end
  | true =>
    match def_name with
    | None => print (concat_list
      [of_string "definition does not appear in "; of_constr statement; of_string "."])
    | Some def_name => print (concat_list
      [of_string "'"; of_string def_name; of_string "'";
        of_string " does not appear in "; of_constr statement; of_string "."])
    end
  end;

  (* Throw error if required *)
  if throw_error
    then throw (of_string "Remove this line in the final version of your proof.")
    else ().

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
      print (of_string "Expanded definition in statements where applicable.");
      print (of_string "To include these statements, use (one of):");

      (* Print unfolded goal *)
      if did_unfold_goal
        then
          print (concat_list [of_string "  We need to show that ";
            of_constr unfolded_goal; of_string "."])
        else ();

      (* Print unfolded hypotheses *)
      if (Bool.neg (_is_empty only_unfolded_hyps))
        then
          let it_holds_msg := fun (x : constr) => concat_list
            [of_string "  It holds that "; of_constr x; of_string "."] in
          List.fold_left (fun _ unfolded_h => print (it_holds_msg unfolded_h))
            only_unfolded_hyps ()
        else ()

    else
      (* Print no statements with definition *)
      match def_name with
      | None => print (of_string "Definition does not appear in any statement.")
      | Some def_name => print (concat_list
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
    - [x : constr option], optional statement in which definitions are to be unfolded.
        If [None], definitions are unfolded in every statement.

  Raises fatal exceptions:
    - [always/none] depending on value of [throw_error].
*)
Ltac2 wp_unfold (unfold_method: constr -> constr)
  (def_name : string option) (throw_error : bool) (x : constr option) :=
  panic_if_goal_wrapped ();
  match x with
  | Some a => unfold_in_statement unfold_method def_name a throw_error
  | None => unfold_in_all unfold_method def_name throw_error
  end.

(* Tactic notation for unfolding generic Gallina terms, not notations.
  For an example of how to used [unfold_in_statement] to unfold notations,
  see [tests/tactics/Unfold.v] *)
Ltac2 Notation "Expand" "the" "definition" "of" targets(list1(seq(reference, occurrences), ","))
  x(opt(seq("in", lconstr))) :=
  wp_unfold (eval_unfold targets) None true x.

(* For now, include optional tail to keep compatible with tactic called by Waterproof editor. *)
Ltac2 Notation "_internal_" "Expand" "the" "definition" "of" targets(list1(seq(reference, occurrences), ",")) x(opt(seq("in", lconstr))) :=
  wp_unfold (eval_unfold targets) None false x.
