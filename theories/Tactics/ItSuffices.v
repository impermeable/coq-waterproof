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
Require Import Waterprove. (* Defines AutomationFailure exception type. *)

Local Ltac2 concat_list (ls : message list) : message :=
  List.fold_right concat (of_string "") ls.

(** Attempts to prove that proposed goal is enough to show current goal.
  If succesful, replaces current goal by proposed goal. *)
Local Ltac2 wp_enough (new_goal : constr) :=
  let err_msg := concat_list
    [of_string "Could not verify that it suffices to show "; of_constr new_goal; of_string "."] in
  match Control.case (fun () =>
    enough $new_goal by (waterprove 5 true [] Main))
  with
  | Val _ => ()
  | Err exn => Control.zero (AutomationFailure err_msg)
  end.

(** Attempts to prove that proposed goal is enough to show current goal,
  given an additional lemma that has to be used in said proof.
  If succesful, replaces current goal by proposed goal. *)
Local Ltac2 wp_enough_by (new_goal : constr) (xtr_lemma : constr) := 
  let err_msg := concat_list
    [of_string "Could not verify that it suffices to show "; of_constr new_goal; of_string "."] in
  match Control.case (fun () =>
    enough $new_goal by 
      (rwaterprove 5 true [fun () => xtr_lemma] Main [xtr_lemma] []))
  with
  | Val _ => ()
  | Err exn => 
    (* check if it would work without lemma *)
    match Control.case (fun () =>
      enough $new_goal by 
        (waterprove 5 true [] Main))
    with
    | Err exn => Control.zero (AutomationFailure err_msg)
    | Val _ =>
      (* problem is the extra lemma: it is not used for proof that new goal is enough *)
      Control.zero (AutomationFailure (concat_list 
        [of_string "Could not verify this follows from "; of_constr xtr_lemma;
          of_string "."]))
    end
  end.


Ltac2 Notation "It" "suffices" "to" "show" that(opt("that")) statement(constr) := 
  panic_if_goal_wrapped ();
  wp_enough statement.


Ltac2 Notation "By" xtr_lemma(constr) "it" "suffices" "to" "show" that(opt("that")) statement(constr) :=
  panic_if_goal_wrapped ();
  wp_enough_by statement xtr_lemma.