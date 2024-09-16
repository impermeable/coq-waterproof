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

open Proofview
open Proofview.Notations

(**
  Checks whether a given evar is a blank in the evar_map.
*)
let is_blank (ev_map : Evd.evar_map) (ev : Evar.t) : bool =
  let EvarInfo ev_info = Evd.find ev_map ev in
  let _, ev_kind = (Evd.evar_source ev_info) in
  match ev_kind with
  | Evar_kinds.QuestionMark _ -> true
  | _ -> false

(**
  A tactic that resturns a list of all evars in a term (= Evd.econstr) that
  were introduced by the user as a blank and have not been resolved yet.
*)
let blank_evars_in_term (term : Evd.econstr) :
  Evar.t list tactic =
  tclEVARMAP >>= fun sigma -> tclUNIT @@
    let evars = Evarutil.undefined_evars_of_term sigma term in
    List.filter (is_blank sigma) (Evar.Set.elements evars)

(** 
  Refines the current goal with just a new named evar, the name of which is
  freshly generated based on the input string.
*)
let refine_goal_with_evar (input : string) : unit tactic =
  let src = (Loc.tag Evar_kinds.GoalEvar) in
  Proofview.Goal.enter begin fun gl ->
    let env = Proofview.Goal.env gl in
    let concl = Proofview.Goal.concl gl in
    Refine.refine ~typecheck:true begin function sigma ->
      let sigma, t = Evarutil.new_evar ~src 
          ~naming:(Namegen.IntroFresh (Names.Id.of_string input))
          env sigma concl in
      (sigma, t)
    end
  end
