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

open Constr
open EConstr
open Hints
open Pp
open Proofview

open Exceptions
open Hint_dataset
open Hint_dataset_declarations
open Wp_auto
open Wp_eauto
open Wp_rewrite

(**
  List of forbidden inductive types
*)
let forbidden_inductive_types: string list = [
  "Coq.Init.Logic.all"; (* forall (should not be necessary) *)
  "Coq.Init.Logic.and"; (* /\ *)
  "Coq.Init.Logic.ex"; (* exists *)
  "Coq.Init.Logic.ex2"; (* exists2 *) 
  "Coq.Init.Logic.or"; (* \/ *)
]

(**
  Is automation shield enabled ? 
*)
let automation_shield: bool ref = Summary.ref ~name:"automation_shield" true

(**
  Returns a [bool] from a [EConstr.constr] indicating if this term is forbidden in automation.

  Forbidden patterns: [forall _, _], [exists _, _], [_ /\ _] and [_ \/ _]
*)
let rec is_forbidden (sigma: Evd.evar_map) (term: constr): bool =
  let exists_in_array (term_array: constr array): bool = Array.exists (fun term -> is_forbidden sigma term) term_array in
  match kind sigma term with
    | Prod (binder, _, _) -> Names.Name.print binder.binder_name <> str "_"
    | Cast (sub_term, _, _) -> is_forbidden sigma sub_term
    | Lambda (_, _, right_side) -> true
    | LetIn (_, value, _, right_side) -> is_forbidden sigma value || is_forbidden sigma right_side
    | App (f, args) -> is_forbidden sigma f || exists_in_array args
    | Case (_, _, params, _, _, c, branches) ->
      is_forbidden sigma c || exists_in_array params || Array.exists (fun (_, branch) -> is_forbidden sigma branch) branches
    | Fix (_, (_, _, bodies)) | CoFix (_, (_, _, bodies)) -> exists_in_array bodies
    | Proj (_, sub_term) -> is_forbidden sigma sub_term
    | Array (_, vals, def, _) -> is_forbidden sigma def || exists_in_array vals
    | Ind ((name, _), _) -> (* [exists], [/\], [\/], ... are defined by inductive types so they are caught here *)
      List.mem (Names.MutInd.print name) @@ List.map str forbidden_inductive_types
    | _ -> false

(**
  Tests that the current goal is not forbidden with the shield on.
*)
let shield_test (): unit tactic =
  Proofview.Goal.enter @@ fun goal ->
    begin
      let sigma = Proofview.Goal.sigma goal in
      let conclusion = Proofview.Goal.concl goal in
      if is_forbidden sigma conclusion then throw (FailedTest "shield");
      tclUNIT ()
    end

(**
  Function that will actually call automation functions
*)
let automation_routine (depth: int) (lems: Tactypes.delayed_open_constr list) (databases: hint_db_name list): unit tactic =
  Tacticals.tclFIRST [
    Tacticals.tclCOMPLETE @@ tclIGNORE @@ wp_auto false depth lems databases;
    Tacticals.tclCOMPLETE @@ tclIGNORE @@ wp_eauto false depth lems databases;
    Tacticals.tclCOMPLETE @@ tclIGNORE @@ wp_autorewrite @@ wp_auto false depth lems databases;
    Tacticals.tclCOMPLETE @@ tclIGNORE @@ wp_autorewrite @@ wp_eauto false depth lems databases
  ]

(**
  Same function as {! automation_routine} but with restricted version of automation functions
*)
let restricted_automation_routine (depth: int) (lems: Tactypes.delayed_open_constr list) (databases: hint_db_name list) (must_use: Pp.t list) (forbidden: Pp.t list): unit tactic =
  Tacticals.tclFIRST [
    Tacticals.tclCOMPLETE @@ tclIGNORE @@ rwp_auto false depth lems databases must_use forbidden;
    Tacticals.tclCOMPLETE @@ tclIGNORE @@ rwp_eauto false depth lems databases must_use forbidden;
    Tacticals.tclCOMPLETE @@ tclIGNORE @@ wp_autorewrite @@ rwp_auto false depth lems databases must_use forbidden;
    Tacticals.tclCOMPLETE @@ tclIGNORE @@ wp_autorewrite @@ rwp_eauto false depth lems databases must_use forbidden
  ]

(**
  Waterprove

  This function is the main automatic solver of coq-waterproof.

  The databases used for the proof search are the one declared in the current imported dataset (see {! Hint_dataset.loaded_hint_dataset}).

  The forbidden patterns are defined in {! is_forbidden}.

  Arguments:
    - [depth] ([int]): max depth of the proof search
    - [shield] ([bool]): if set to [true], will stop the proof search if a forbidden pattern is found
    - [lems] ([Tactypes.delayed_open_constr list]): additional lemmas that are given to solve the proof
    - [database_type] ([Hint_dataset_declarations]): type of databases that will be use as hint databases
*)
let waterprove (depth: int) ?(shield: bool = false) (lems: Tactypes.delayed_open_constr list) (database_type: database_type): unit tactic =
  Proofview.Goal.enter @@ fun goal ->
    begin
      let sigma = Proofview.Goal.sigma goal in
      let conclusion = Proofview.Goal.concl goal in
      tclORELSE
        (automation_routine 2 lems (get_current_databases database_type))
        begin fun _ ->
          if shield && !automation_shield && is_forbidden sigma conclusion then throw (FailedAutomation "The current goal cannot be proved since it contains shielded patterns");
          automation_routine depth lems (get_current_databases database_type)
        end
    end

(**
  Restricted Waterprove

  This function is similar to {! waterprove} but use {! wp_auto.rwp_auto} and {! wp_eauto.rwp_eauto} instead of {! wp_auto.wp_auto} and {! wp_eauto.wp_eauto}.

  Arguments:
    - [depth] ([int]): max depth of the proof search
    - [shield] ([bool]): if set to [true], will stop the proof search if a forbidden pattern is found
    - [lems] ([Tactypes.delayed_open_constr list]): additional lemmas that are given to solve the proof
    - [database_type] ([Hint_dataset_declarations]): type of databases that will be use as hint databases
    - [must_use] ([string list]): list of hints that have to be used during the automatic solving
    - [forbidden] ([string list]): list of hints that must not be used during the automatic solving
*)
let rwaterprove (depth: int) ?(shield: bool = false) (lems: Tactypes.delayed_open_constr list) (database_type: database_type) (must_use: constr list) (forbidden: constr list): unit tactic =
  Proofview.Goal.enter @@ fun goal ->
    begin
      let env = Proofview.Goal.env goal in
      let sigma = Proofview.Goal.sigma goal in
      let conclusion = Proofview.Goal.concl goal in
      let must_use_tactics = List.map (Printer.pr_econstr_env env sigma) must_use in
      let forbidden_tactics = List.map (Printer.pr_econstr_env env sigma) forbidden in
      tclORELSE
        (restricted_automation_routine 2 lems (get_current_databases database_type) must_use_tactics forbidden_tactics)
        begin fun _ ->
          if shield && !automation_shield && is_forbidden sigma conclusion then throw (FailedAutomation "The current goal cannot be proved since it contains shielded patterns");
          restricted_automation_routine depth lems (get_current_databases database_type) must_use_tactics forbidden_tactics
        end
    end