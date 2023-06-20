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

Require Import Util.Init.

(** get_value_of_hyp_id
    
  Given an [constr] that is the reference of a hypothesis (i.e. the LHS in the proof context, e.g. the [h] in [h: 1 + 1 = 2]), return the unnormalized value of the hypothesis.

  Arguments:
    - [hyp: constr], LHS of the hypothsis.

  Returns:
    - [constr]: unnormalized type of the hypothesis (i.e. the RHS).
*)
Ltac2 get_value_of_hyp (hyp: constr) :=
  eval unfold type_of in (type_of $hyp).

(** * get_value_of_hyp_id

  Given an [ident] matching a hypothesis, return the unnormalized value of the hypothesis.

  Arguments:
    - [hyp_id: ident], name of hypothesis.

  Returns:
    - [constr]: unnormalized type of the hypothesis.
*)
Ltac2 get_value_of_hyp_id (hyp_id: ident) :=
  let h := Control.hyp hyp_id in
  get_value_of_hyp h.