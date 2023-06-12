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

val wp_autorewrite :
  string list ->
  Locus.clause ->
  unit Proofview.tactic ->
  unit Proofview.tactic

val print_rewrite_hintdb :
  Environ.env -> Evd.evar_map -> string -> Pp.t

(**
  This function will add in the rewrite hint database "core" every hint possible created from the hypothesis
*)
val fill_local_rewrite_database :
  unit -> unit Proofview.tactic

val clear_rewrite_database :
  unit -> unit