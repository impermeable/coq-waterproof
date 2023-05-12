open Constr
open EConstr
open Exninfo
open Hints
open Pp
open Proofview
open Proofview.Notations

open Exceptions
open Hint_dataset
open Hint_dataset_declarations
open Wauto
open Weauto

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
  Returns a [bool] from a [EConstr.constr] indicating if this term is forbidden in automation.

  Forbidden patterns: [forall _, _], [exists _, _], [_ /\ _] and [_ \/ _]
*)
let rec is_forbidden (sigma: Evd.evar_map) (term: constr): bool =
  let exists_in_array (term_array: constr array): bool = Array.exists (fun term -> is_forbidden sigma term) term_array in
  match kind sigma term with
    | Prod (binder, _, _) -> Names.Name.print binder.binder_name <> str "_"
    | Cast (sub_term, _, _) -> is_forbidden sigma sub_term
    | Lambda (_, _, right_side) -> is_forbidden sigma right_side
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

let automation_routine (depth: int) (lems: Tactypes.delayed_open_constr list) (databases: hint_db_name list): unit tactic =
  tclORELSE
    begin
      tclIGNORE @@ wauto false depth lems databases <*>
      tclIGNORE @@ weauto false depth lems databases
    end
    begin
      fun (exn, info) ->
        throw (FailedAutomation (
          match get_backtrace info with
            | None -> "could not find a proof for the current goal"
            | Some backtrace -> backtrace_to_string backtrace
        ))
    end

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
      if is_forbidden sigma conclusion then throw (FailedAutomation "The current goal cannot be proved since it contains shielded patterns");
      automation_routine depth lems (get_current_databases database_type)
    end
