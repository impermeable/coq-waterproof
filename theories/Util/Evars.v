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

Require Export Ltac2.Ltac2.

Require Import Waterproof.Waterproof.

Ltac2 @ external make_evar_from_constr : string -> unit := "coq-waterproof" "make_evar_from_constr_external".

Ltac2 @ external get_evar_list_in_term : constr -> evar list := "coq-waterproof" "evar_list_from_term_external".

Ltac2 rename_blank_evars_in_term (base_name : string) (x : constr) :=
  let evars := get_evar_list_in_term x in
  let m := List.length evars in
  List.fold_left (fun _ ev => Control.new_goal ev) (evars) ();
  Control.focus 2 (Int.add m 1) (fun () => make_evar_from_constr base_name; Control.shelve()).
