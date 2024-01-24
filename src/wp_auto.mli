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

open Backtracking

(**
  Same function as {! Auto.exists_evaluable_reference}
*)
val exists_evaluable_reference : Environ.env -> Names.Evaluable.t -> bool

(**
  Prints "idtac" if the [log] field is [true]
*)
val pr_info_nop : unit -> unit

(**
  Tries the given tactic and calls an info printer if it fails
*)
val tclTryDbg :
  (unit -> unit) ->
  trace Proofview.tactic ->
  trace Proofview.tactic

(**
  Creates a function that takes a hint database and returns a hint list
*)
val hintmap_of :
  Environ.env ->
  Evd.evar_map ->
  Names.Id.Pred.t ->
  Evd.econstr ->
  Hints.hint_db ->
  Hints.FullHint.t list

(**
  Searches a sequence of at most [n] tactics within [db_list] and [lems] that solves the goal

  The goal cannot contain evars
*)
val search :
  Backtracking.trace ->
  int ->
  Tactypes.delayed_open_constr list ->
  Hints.hint_db list ->
  Pp.t list ->
  Pp.t list ->
  Backtracking.trace Proofview.tactic

(**
  Waterproof auto

  This function is a rewrite around {! Auto.auto} with the same arguments to be able to retrieve which hints have been used in case of success.

  Returns a typed tactic containing the full trace
*)
val wp_auto :
  bool ->
  int ->
  Tactypes.delayed_open_constr list ->
  string list ->
  Backtracking.trace Proofview.tactic

(**
  Restricted Waterproof auto

  This function acts the same as {! wp_auto} but will fail if all proof found contain at least one must-use lemma that is unused or one hint that is in the [forbidden] list.
*)
val rwp_auto :
  bool ->
  int ->
  Tactypes.delayed_open_constr list ->
  string list ->
  Pp.t list ->
  Pp.t list ->
  Backtracking.trace Proofview.tactic
