val loaded_hint_dataset : string Summary.Local.local_ref

val load_dataset : string -> unit

val positive_databases : unit -> Hints.hint_db_name list
val negative_databases : unit -> Hints.hint_db_name list
val decidability_databases : unit -> Hints.hint_db_name list
val shorten_databases : unit -> Hints.hint_db_name list