(**
  Interface to load and unload usual hint databases such as reals, integers, classical logic, ...
*)
type hint_dataset = {
  name : string;
  positive_databases : string list;
  negative_databases : string list;
  decidability_databases : string list;
  shorten_databases : string list;
}

val empty : hint_dataset
val core : hint_dataset
val algebra : hint_dataset
val integers : hint_dataset
val reals_and_integers : hint_dataset
val sets : hint_dataset
