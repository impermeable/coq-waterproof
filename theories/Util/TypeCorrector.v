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

Require Import Util.Init.
Require Import Util.MessagesToUser.

From Ltac2 Require Import Ltac2 Message.

Local Ltac2 concat_list (ls : message list) : message :=
  List.fold_right concat (of_string "") ls.

(** Ensures that the type of [t] can be used in type matching or asserting. *)
Ltac2 correct_type_by_wrapping (t: constr): constr :=
  let type_t := Constr.type t in
  match! type_t with
    | Prop => t
    | Set => t 
    | Type => t
    | bool => constr:(is_true $t)
    | _ => throw (concat_list [
      of_string "Expected a term with type in ['Prop', 'Set', 'Type', 'bool'], but we got a term of type '";
      of_constr type_t; 
      of_string "' instead."]); constr:(tt)
  end.