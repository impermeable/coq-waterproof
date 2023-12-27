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

Require Import Util.Init.
Require Import Util.Goals.
Require Import Util.Since.
Require Import Util.MessagesToUser.
Require Import Waterprove.

Local Ltac2 concat_list (ls : message list) : message :=
  List.fold_right concat (of_string "") ls.

(** Attempts to prove that proposed goal is enough to show current goal.
  If succesful, replaces current goal by proposed goal. *)
Local Ltac2 wp_enough (new_goal : constr) :=
  let err_msg := concat_list
    [of_string "Could not verify that it suffices to show "; of_constr new_goal; of_string "."] in
  match Control.case (fun () =>
    enough $new_goal by (waterprove 5 true Main))
  with
  | Val _ => ()
  | Err (FailedToProve _) => throw err_msg
  | Err exn => Control.zero exn
  end.
  

(** Attempts to prove that proposed goal is enough to show current goal,
  given an additional lemma that has to be used in said proof.
  If succesful, replaces current goal by proposed goal. *)
Local Ltac2 core_wp_enough_by (new_goal : constr) (xtr_lemma : constr) := 
  let err_msg := concat_list
    [of_string "Could not verify that it suffices to show "; of_constr new_goal; of_string "."] in
  match Control.case (fun () =>
    enough $new_goal by 
      (rwaterprove 5 true Main xtr_lemma))
  with
  | Val _ => ()
  | Err (FailedToProve _) => throw err_msg
  | Err exn => Control.zero exn (* includes FailedToUse error *)
  end.

(** Adaptation of [core_wp_enough_by] that turns the [FailedToUse] errors 
  which might be thrown into user readable errors. *)
Local Ltac2 wp_enough_by (claim : constr) (xtr_lemma : constr) :=
  wrapper_core_by_tactic (core_wp_enough_by claim) xtr_lemma.

(** Adaptation of [core_wp_assert_by] that allows user to use mathematical statements themselves
  instead of references to them as extra information for the automation system.
  Uses the code in [Since.v]. *)
Local Ltac2 wp_enough_since (claim : constr) (xtr_claim : constr) :=
  since_framework (core_wp_enough_by claim) xtr_claim.

Ltac2 Notation "It" "suffices" "to" "show" that(opt("that")) statement(constr) := 
  panic_if_goal_wrapped ();
  wp_enough statement.


Ltac2 Notation "By" xtr_lemma(constr) "it" "suffices" "to" "show" that(opt("that")) statement(constr) :=
  panic_if_goal_wrapped ();
  wp_enough_by statement xtr_lemma.

Ltac2 Notation "Since" xtr_claim(constr) "it" "suffices" "to" "show" that(opt("that")) statement(constr) :=
  panic_if_goal_wrapped ();
  wp_enough_since statement xtr_claim.