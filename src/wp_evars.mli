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

val print_evars : Ltac2_plugin.Tac2ffi.valexpr Proofview.tactic

val print_evar_info : Evar.t -> Ltac2_plugin.Tac2ffi.valexpr Proofview.tactic

val find_evars_in_term : Evd.econstr -> Ltac2_plugin.Tac2ffi.valexpr Proofview.tactic

val make_new_evar_tac : Evar.t -> unit Proofview.tactic

val make_evar_from_constr : string -> unit Proofview.tactic