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

(**
  Checks whether a given evar is a blank in the evar_map.
*)
val is_blank : Evd.evar_map -> Evar.t -> bool

(** 
  Refines the current goal with just a new named evar, the name of which is
  based on the input string.
*)
val refine_goal_with_evar : string -> unit Proofview.tactic

(**
  A tactic that resturns a list of all evars in a term (= Evd.econstr) that
  were introduced by the user as a blank and have not been resolved yet.
*)
val evar_list_from_term : Evd.econstr -> Evar.t list Proofview.tactic
