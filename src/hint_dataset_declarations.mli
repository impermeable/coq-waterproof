(**
  Interface to load and unload usual hint databases such as reals, integers, classical logic, ...
*)
type hint_dataset

(**
  Type referencing all database lists that a {! hint_dataset} should contain
*)
type database_type = Positive | Negative | Decidability | Shorten

(**
  Returns the name of the given [dataset]
*)
val name : hint_dataset -> string

(**
  Returns the list of databases for the given {! database_type}
*)
val get_databases : hint_dataset -> database_type -> Hints.hint_db_name list

val empty : hint_dataset
val core : hint_dataset
val algebra : hint_dataset
val integers : hint_dataset
val reals_and_integers : hint_dataset
val sets : hint_dataset
