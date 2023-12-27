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

Require Import Util.Constr.
Require Import Util.Goals.

Local Ltac2 my_assert (t:constr) (id:ident option) := 
  match id with
    | None =>
      let h := Fresh.in_goal @_H in
      ltac2_assert h t
    | Some id => ltac2_assert id t
  end.

Ltac2 Notation "We" "claim" "that" t(constr) id(opt(seq("(", ident, ")"))) :=
  panic_if_goal_wrapped ();
  my_assert t id.