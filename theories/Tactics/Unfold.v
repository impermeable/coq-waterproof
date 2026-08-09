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
(* Bring the English notations of these tactics into scope: they are used
   internally below (in suggestions tested via [Control.case]). *)
Import ItSuffices.English.
Import ItHolds.English.
Local Ltac2 concat_list (ls : message list) : message :=
  List.fold_right concat ls (of_string "").

Require Import Util.Goals.
Require Import Util.MessagesToUser.

Ltac2 Type unfold_action := [
  | Unfold (string, reference)
  | Apply (string, constr)
  | Rewrite (string, constr)
].

Ltac2 @ external extract_def_ffi : string -> reference option := "rocq-runtime.plugins.coq-waterproof" "extract_def_external".
Ltac2 @ external find_unfolds_by_str_ffi : string -> unfold_action list := "rocq-runtime.plugins.coq-waterproof" "find_unfold_by_str_external".
Ltac2 @ external find_unfolds_by_ref_ffi : reference -> unfold_action list := "rocq-runtime.plugins.coq-waterproof" "find_unfold_by_ref_external".

Ltac2 @ external get_unfold_references_ffi : unit -> reference list := "rocq-runtime.plugins.coq-waterproof" "get_unfold_references_external".


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
      | [|- _] => throw (tr [("en", "Unexpected error in tactic_in_constr. Please report."); ("fr", "Erreur inattendue dans tactic_in_constr. Veuillez le signaler.")]); constr:(False)
      end in
      intro;
      exact I;
      rewritten_term)
    ) in
  clear $h;
  return_term.

Ltac2 unfold_method_for_action (ua : unfold_action) (stmt : constr) : constr :=
  match ua with
  | Unfold _ name => eval unfold $name in $stmt
  | Apply _ equiv => apply_in_constr equiv stmt
  | Rewrite _ eq => tactic_in_constr eq stmt
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
  (def_name : string option) (throw_error : bool) (definitional : bool) (notify_if_not_present : bool) :=
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
      match def_name with
      | Some s => info_notice (of_string (String.concat "" [s; ":"]))
      | _ => ()
      end;

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
            (print_tactic (concat_list [tr [("en", "We need to show that "); ("fr", "Nous devons montrer que ")];
              of_lconstr unfolded_goal; of_string "."]))
          else
            match Control.case (fun () => It suffices to show that $unfolded_goal; Control.zero Succeeded) with
            | Err Succeeded => (print_tactic (concat_list [tr [("en", "It suffices to show that "); ("fr", "Il suffit de montrer que ")];
                                of_lconstr unfolded_goal; of_string "."]))
            | _ => warn (concat_list [tr [("en", "The following suggestion will likely not work,"); ("fr", "La suggestion suivante ne fonctionnera probablement pas,")];
            tr [("en", " (this is probably caused by a misalignment in the automation for"); ("fr", " (ceci est probablement dû à un désalignement dans l'automatisation pour")];
            tr [("en", " unfolding statements. Please notify your teacher or the Waterproof developers):"); ("fr", " le déroulement des énoncés. Veuillez prévenir votre enseignant ou les développeurs de Waterproof) :")]; fnl(); tr [("en", "It suffices to show that "); ("fr", "Il suffit de montrer que ")];
                                of_lconstr unfolded_goal; of_string "."])
            end
        else ();

      (* Print unfolded hypotheses *)
      if (Bool.neg (_is_empty only_unfolded_hyps))
        then
          let it_holds_msg := fun (x : constr) => concat_list
            [tr [("en", "It holds that "); ("fr", "Il s'avère que ")]; of_lconstr x; of_string "."] in
          let test_and_print unfolded_h :=
            match Control.case (fun () => It holds that $unfolded_h; Control.zero Succeeded) with
            | Err Succeeded => print_tactic (it_holds_msg unfolded_h)
            | _ => warn (concat_list [tr [("en", "The following suggestion will likely not work,"); ("fr", "La suggestion suivante ne fonctionnera probablement pas,")];
            tr [("en", " (this is probably caused by a misalignment in the automation for"); ("fr", " (ceci est probablement dû à un désalignement dans l'automatisation pour")];
            tr [("en", " unfolding statements. Please notify your teacher or the Waterproof developers):"); ("fr", " le déroulement des énoncés. Veuillez prévenir votre enseignant ou les développeurs de Waterproof) :")]; fnl(); it_holds_msg unfolded_h])
            end in
          if definitional then
            (List.iter (fun unfolded_h => print_tactic (it_holds_msg unfolded_h))) only_unfolded_hyps
          else
            (List.iter test_and_print only_unfolded_hyps)
        else ()

    else
      (* Print no statements with definition *)
      if (Bool.and notify_if_not_present definitional) then
        (match def_name with
        | None => info_notice (tr [("en", "Definition does not appear in any statement."); ("fr", "La définition n'apparaît dans aucun énoncé.")])
        | Some def_name => info_notice (concat_list
            [of_string "'"; of_string def_name; of_string "'";
              tr [("en", " cannot be used in any statement."); ("fr", " ne peut être utilisé dans aucun énoncé.")]])
        end) else ();

  (* Throw error if required *)
  if throw_error
    then throw (tr [("en", "Remove this line in the final version of your proof."); ("fr", "Supprimez cette ligne dans la version finale de votre preuve.")])
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
  (judgmental : bool) (notify_if_not_present : bool) :=
  panic_if_goal_wrapped ();
  unfold_in_all unfold_method def_name throw_error judgmental notify_if_not_present.

(* TODO: Refactor unfold system to be more maintainable *)

Ltac2 name_from_action (ua : unfold_action) : string :=
  match ua with
  | Unfold name _ => name
  | Apply name _ => name
  | Rewrite name _ => name
  end.

Local Ltac2 wp_unfold_from_action_list (ua_list : unfold_action list)
  (notify_if_not_present : bool) :=
  let definitional_for_action (ua : unfold_action) := match ua with
  | Unfold _ _ => true
  | Apply _ _ => false
  | Rewrite _ _ => false
  end in
  List.iter (fun z =>
      wp_unfold (unfold_method_for_action z)
      (Some (name_from_action z)) false (definitional_for_action z) notify_if_not_present)
    ua_list.


Ltac2 wp_unfold_by_string (s : string) (notify_if_not_present : bool) :=
  wp_unfold_from_action_list (find_unfolds_by_str_ffi s) notify_if_not_present.

Ltac2 wp_unfold_by_ref (r : reference) (notify_if_not_present : bool) :=
  let unfold_list := find_unfolds_by_ref_ffi r in
  let unfold_list := match unfold_list with
    | [] => [Unfold (String.concat " " ["Definition"; shortest_string_of_global_ffi r]) r]
    | _ => unfold_list
    end in
  wp_unfold_from_action_list unfold_list notify_if_not_present.

Ltac2 wp_expand (r : reference) :=
  wp_unfold_by_ref r true;
  throw (tr [("en", "Remove this line in the final version of your proof."); ("fr", "Supprimez cette ligne dans la version finale de votre preuve.")]).

Ltac2 wp_expand_deprecated (r : reference) :=
  warn (tr [("en", "Warning: The notation 'Expand the definition of' is deprecated. Please use 'Expand' instead."); ("fr", "Attention : la notation « Développons la définition de » est obsolète. Veuillez utiliser « Développons » à la place.")]);
  wp_expand r.

(**
  Attempts to unfold definition(s) in statements according to unfold actions that have
  been pre-stored in a database.

  Here are some examples of syntax for adding unfold actions to the database.
  For more examples, see [tests/tactics/Unfold.v].

  [Waterproof Register Unfold "converges" "to" converges_to.
  Waterproof Register Unfold Apply "infimum" is_infimum ; (alt_char_inf).
  Waterproof Register Unfold Rewrite "powerRZ" powerRZ ; (powerRZ_Rpower).]
*)
Module English.

  Ltac2 Notation "Expand" x(reference) :=
    wp_expand x.

  (** Deprecated version of this notation *)
  Ltac2 Notation "Expand" "the" "definition" "of" x(reference) :=
    wp_expand_deprecated x.

  (** Unfold all occurences of all registered definitions and alternative characterizations. *)
  Ltac2 Notation "Expand" "All" :=
    let ls := get_unfold_references_ffi () in
    List.iter (fun l => wp_unfold_by_ref l false) ls;
    throw (tr [("en", "Remove this line in the final version of your proof."); ("fr", "Supprimez cette ligne dans la version finale de votre preuve.")]).

End English.

Export English.

Module French.

  Ltac2 Notation "Développons" x(reference) :=
    wp_expand x.

  (** Version dépréciée de cette notation *)
  Ltac2 Notation "Développons" "la" "définition" "de" x(reference) :=
    wp_expand_deprecated x.

  (** Développe toutes les occurrences de toutes les définitions et caractérisations alternatives enregistrées. *)
  Ltac2 Notation "Développons" "tout" :=
    let ls := get_unfold_references_ffi () in
    List.iter (fun l => wp_unfold_by_ref l false) ls;
    throw (tr [("en", "Remove this line in the final version of your proof."); ("fr", "Supprimez cette ligne dans la version finale de votre preuve.")]).

End French.
