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

Require Import Waterproof.Tactics.Help.

Local Ltac2 my_assert (t:constr) (id:ident option) := 
  (* Fixed by fixing the ltac2_assert *)
  match id with
    | None =>
      let h := Fresh.in_goal @_H in
      ltac2_assert h t
    | Some id => ltac2_assert id t
  end.

Ltac2 Notation "We" "claim" "that" t(lconstr) id(opt(seq("as", "(", ident, ")"))) :=
  panic_if_goal_wrapped ();
  (* Print suggestion on how to use new statement (after it is proven). *)
  HelpNewHyp.suggest_how_to_use_after_proof t id;
  my_assert t id.