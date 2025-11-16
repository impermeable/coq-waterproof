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

From Waterproof Require Import Util.Constr.
From Waterproof Require Import Util.Goals.
From Waterproof Require Import Util.Hypothesis.
From Waterproof Require Import Util.MessagesToUser.

Require Import Notations.Sets.
Open Scope subset_scope.


(** Given a forall- or exists-statement, prints suggestion how to use it. *)

Ltac2 suggest_how_to_use (x : constr) (label : ident option) :=
  if Bool.neg (get_print_hypothesis_flag ()) then ()
  else
  let print_forall_msg () :=
    info_notice (concat_list [
        of_string "To use "; of_constr x; of_string ", consider:"]);
      let template := match label with
        | None => "Use ${0:x} := ${1:0} in (${2:0 = 0}).${3}"
        | Some i => String.concat "" ["Use ${0:x} := ${1:0} in ("; Ident.to_string i; ").${2}"]
      end in
      insert_msg "Use ... := ... in ...." template in
  let print_exists_msg () :=
    info_notice (concat_list [
        of_string "To use "; of_constr x; of_string ", consider:"]);
      insert_msg "Obtain ... according to ...." "Obtain ${0:x} according to (${1:i}).${2}" in
  lazy_match! x with
  | _ -> ?_b => ()
  | forall _, _ => print_forall_msg ()
  | ∀ _ _ , _ => print_forall_msg ()
  | ∀ _ > _ , _ => print_forall_msg ()
  | ∀ _ ≥ _, _ => print_forall_msg ()
  | ∀ _ < _ , _ => print_forall_msg ()
  | ∀ _ ≤ _, _ => print_forall_msg ()
  | exists _, _ => print_exists_msg ()
  | ∃ _ _, _ => print_exists_msg ()
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
  let print_forall_msg () :=
    info_notice (concat_list [
        of_string "After proving "; of_constr x; of_string ", consider:"]);
      let template := match label with
        | None => "Use ${0:x} := ${1:0} in (${2:i}).${3}"
        | Some i => String.concat "" ["Use ${0:x} := ${1:0} in ("; Ident.to_string i; ").${2}"]
      end in
      insert_msg "Use ... := ... in ...." template in
  let print_exists_msg () :=
    info_notice (concat_list [
        of_string "After proving "; of_constr x; of_string ", consider:"]);
      insert_msg "Obtain such a ...." "Obtain such a ${0:x}.${1}" in
  lazy_match! x with
  | _ -> ?_b => ()
  | forall _, _ => print_forall_msg ()
  | ∀ _ _, _ => print_forall_msg ()
  | ∀ _ > _, _ => print_forall_msg ()
  | ∀ _ ≥ _, _ => print_forall_msg ()
  | exists _, _ => print_exists_msg ()
  | ∃ _ _, _ => print_exists_msg ()
  | ∃ _ > _, _ => print_exists_msg ()
  | ∃ _ ≥ _, _ => print_exists_msg ()
  | _ => ()
  end.
