(**
  Contains the hint dataset that is currently loaded
*)
val loaded_hint_dataset : string ref

(**
  Replace all current loaded hints by the ones declared in the [hint_dataset]
*)
val load_dataset : string -> unit

(**
  Returns the current positive databases
*)
val positive_databases : unit -> Hints.hint_db_name list

(**
  Returns the current negative databases
*)
val negative_databases : unit -> Hints.hint_db_name list

(**
  Returns the current decidability databases
*)
val decidability_databases : unit -> Hints.hint_db_name list

(**
  Returns the current shorten databases
*)
val shorten_databases : unit -> Hints.hint_db_name list