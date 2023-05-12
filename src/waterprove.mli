(**
  Returns a [bool] from a [EConstr.constr] indicating if this term is forbidden in automation.

  Forbidden patterns: [forall _, _], [exists _, _], [_ /\ _] and [_ \/ _]
*)
val is_forbidden : Evd.evar_map -> EConstr.constr -> bool

(**
  Tests that the current goal is not forbidden with the shield on.
*)
val shield_test : unit -> unit Proofview.tactic

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
val waterprove :
  int ->
  ?shield:bool ->
  Tactypes.delayed_open_constr list ->
  Hint_dataset_declarations.database_type ->
  unit Proofview.tactic
