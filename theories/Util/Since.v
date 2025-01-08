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
  List.fold_right concat ls (of_string "").

Require Import Util.Constr.
Require Import Util.MessagesToUser.
Require Import Waterprove.

Require Import Util.Init.
Require Import Util.TypeCorrector.
Require Import Notations.Sets.

Local Ltac2 get_type (x: constr) : constr := eval unfold type_of in (type_of $x).

Local Ltac2 check_if_not_reference (x : constr) :=
  let type_x := get_type x in
  match! type_x with
  | Prop => ()
  | Set => ()
  | Type => ()
  | _ => throw (concat_list
        [of_string "Cannot use reference "; of_constr x; of_string " with `Since`.
Try `By "; of_constr x; of_string " ...` instead."])
  end.

Local Ltac2 check_if_not_statement (x : constr) :=
  let err_msg := concat_list
    [of_string "Cannot use statement "; of_constr x; of_string " with `By`.
Try `Since "; of_constr x; of_string " ...` instead."]
  in
  let type_x := get_type x in
  match! type_x with
  | Prop => throw err_msg
  | Set => throw err_msg
  | Type => throw err_msg
  | _ => ()
  end.


(** Attempts to prove [claimed_cause] with minimal automation,
  and then executes [by_tactic] with the proof of [claimed_cause]
  as an argument.
  Expects that [by_tactic] can throw a [(Waterprove.)FailedToUse] error,
  those errors are caught; the extra lemma that the automation failed to use
  is used in a new error that is thrown.
*)

Ltac2 since_framework (by_tactic : constr -> unit) (claimed_cause : constr) :=
  (* Wrap in is_true if needed *)
  let claimed_cause := correct_type_by_wrapping claimed_cause in
  (* first, check if [claimed_cause] is a statement. *)
  check_if_not_reference claimed_cause;

  let id_cause := Fresh.in_goal @_temp in
  (* attempt to prove [claimed_cause]*)
  match Control.case (fun () =>
    let unsealed_claimed_cause := eval unfold seal in $claimed_cause in
    assert $unsealed_claimed_cause as $id_cause by
      (waterprove 1 true Shorten))
  with
  | Err (FailedToProve _) =>
    throw (concat_list
      [of_string "State that "; of_constr claimed_cause; of_string " holds";
       of_string " before using it in `Since ...`."])
  | Err exn => Control.zero exn
  | Val _ =>
    (* use proof of [claimed_cause] in [by_tactic] *)
    let cause := Control.hyp id_cause in
    match Control.case (fun () =>
      by_tactic cause)
    with
    | Val _ => clear $id_cause
    | Err (FailedToUse h) =>
      let type_h := (get_type h) in
      clear $id_cause;
      throw (concat_list
        [of_string "Could not verify this follows from "; of_constr type_h; of_string "."])
    | Err exn => clear $id_cause; Control.zero exn
    end
  end.

Ltac2 unseal_lemma (xtr_lemma : constr) : ident :=
  let aux_id := Fresh.fresh (Fresh.Free.of_goal ()) @_aux in
  let statement_xtr_lemma := Constr.type xtr_lemma in
  let unsealed_statement := eval unfold seal in $statement_xtr_lemma in
  assert $unsealed_statement as $aux_id;
  Control.focus 1 1 (fun () => exact $xtr_lemma);
  aux_id.

(** Wrapper for the main functionality of 'By ...'-tactics,
  such that the main fucntionality can be reused in 'Since ...'-tactics.

  Checks whether [xtr_lemma] is not a statement (i.e. not a Prop/Set/Type) and
  catches [(Waterprove.)FailedToUse] errors to turn them into user-readable errors. *)
Ltac2 wrapper_core_by_tactic (by_tactic : constr -> unit) (xtr_lemma : constr) :=
  check_if_not_statement xtr_lemma;
  (* check if necessary to unseal. Because we are adding to the local
    hypothesis if we need to unseal, this interferes with our
    capability to check whether a lemma is used... *)
  (* TODO: does this need to move away from here? *)
  let xtr_lemma_contains_seal :=
    match! (Constr.type xtr_lemma) with
    | context [seal _ _ ] => true
    | _ => false
    end in
  let (opt_id, aux_lemma) :=
    if xtr_lemma_contains_seal then
      let aux_id := unseal_lemma xtr_lemma in
      (Some aux_id, Control.hyp aux_id)
    else (None, xtr_lemma) in
  match Control.case (fun () => by_tactic aux_lemma) with
  | Val _ => ()
  | Err (FailedToUse h) => throw (concat_list
      [of_string "Could not verify this follows from "; of_constr h; of_string "."])
  | Err exn => Control.zero exn
  end;
  match opt_id with
  | Some id => Std.clear [id]
  | _ => ()
  end.
