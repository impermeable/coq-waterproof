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

From Ltac2 Require Import Ltac2.
From Stdlib Require Import String.


From Waterproof Require Import ConvertStrings.
From Waterproof Require Import ItHolds.
From Waterproof Require Import Conclusion.
From Waterproof Require Import ItSuffices.
From Waterproof Require Import Goals.

Local Ltac2 parse_arguments (x1 : constr)
  (x2 : ((constr list) option * constr) option) :=
  match x2 with
  | Some (lst_opt, xtr) =>
      let xtr_reasons :=
        match lst_opt with
        | Some lst => lst
        | None => []
        end
      in
    List.concat [[x1]; xtr_reasons; [xtr]]
  | None => [x1]
  end.

Ltac2 Notation "it" "holds" : 0 := "it holds".
Ltac2 Notation "we" "conclude" : 3 := "we conclude".
Ltac2 Notation "it" "suffices" "to" "show" : 0 := "it suffices".

Ltac2 Notation "By"
  first_term(lconstr)
  x2(opt(
    seq(
      opt(seq(",", list1(lconstr, ","))),
      seq("and", lconstr)
    )
  )) x(tactic) "that" claim(lconstr) label(opt(seq("as", "(", ident, ")")))  :=
  let parsed_args := parse_arguments first_term x2 in
  let xtr_lemmas := List.filter_out (fun z => Constr.equal (Constr.type z) constr:(string)) parsed_args in
  let xtr_dbs := List.filter (fun z => Constr.equal (Constr.type z) constr:(string)) parsed_args in
  let xtr_dbs := List.map rocq_string_to_ltac2_string xtr_dbs in
  if String.equal x "it holds" then
    (wp_assert_by_with_checks claim label xtr_lemmas xtr_dbs)
  else if String.equal x "we conclude" then
    (wp_conclude_by_with_checks claim xtr_lemmas xtr_dbs)
  else
    (wp_enough_by_with_checks claim xtr_lemmas xtr_dbs).
