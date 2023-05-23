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
  Searches a sequence of at most [n] tactics within [db_list] and [lems] that solves the goal

  The goal can contain evars
*)
val esearch :
  bool ->
  int ->
  Tactypes.delayed_open_constr list ->
  Hints.hint_db list ->
  Backtracking.trace Proofview.tactic

(**
  Waterproof eauto

  This function is a rewrite around coq-core.Eauto.eauto with the same arguments to be able to retrieve which tactics have been used in case of success.

  The given [debug] will be updated with the trace at the end of the execution (consider using).

  The code structure has been rearranged to match the one of [Wauto.wauto].
*)
val weauto :
  bool ->
  int ->
  Tactypes.delayed_open_constr list ->
  string list ->
  Backtracking.trace Proofview.tactic

(**
  Restricted Waterproof eauto

  This function acts the same as {! wauto} but will fail if all proof found contain at least one must-use lemma that is unused or one hint that is in the [forbidden] list.
*)
val rweauto :
  bool ->
  int ->
  Tactypes.delayed_open_constr list ->
  Hints.hint_db_name list ->
  Pp.t list ->
  Pp.t list ->
  Backtracking.trace Proofview.tactic