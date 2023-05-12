(**
  Contains the hint dataset that is currently loaded
*)
val loaded_hint_dataset : string ref

(**
  Complete list of all existing dataset names
*)
val existing_dataset_names: string list

(**
  Replace all current loaded hints by the ones declared in the [hint_dataset]
*)
val load_dataset : string -> unit

(**
  Returns the list of databases of the current loaded dataset for the given {! Hint_dataset_declarations.database_type}
*)
val get_current_databases : Hint_dataset_declarations.database_type -> Hints.hint_db_name list