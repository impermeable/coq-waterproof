open Hints

(**
  Interface to load and unload usual hint databases such as reals, integers, classical logic, ...
*)
type hint_dataset = {
  name: string; (** Dataset name *)
  positive_databases: hint_db_name list; (** Databases that will be called to solve a goal *)
  negative_databases: hint_db_name list; (** Databases that will be called to solve a goal containing a negation *)
  decidability_databases: hint_db_name list; (** Databases that can be called to solve a goal with decidability properties *)
  shorten_databases: hint_db_name list; (** Databases that will be called to solve a goal faster than [positive_databases] *)
}

(**
  Type referencing all database lists that a {! hint_dataset} should contain
*)
type database_type = Positive | Negative | Decidability | Shorten

(**
  Returns the name of the given [dataset]
*)
let name (dataset: hint_dataset): string = dataset.name

(**
  Returns the list of databases for the given {! database_type}
*)
let get_databases (dataset: hint_dataset) (databases: database_type): hint_db_name list = match databases with
  | Positive -> dataset.positive_databases
  | Negative -> dataset.negative_databases
  | Decidability -> dataset.decidability_databases
  | Shorten -> dataset.shorten_databases

let empty: hint_dataset = {
  name = "Empty";
  positive_databases: hint_db_name list = ["nocore"];
  negative_databases: hint_db_name list = ["nocore"];
  decidability_databases: hint_db_name list = ["nocore"];
  shorten_databases: hint_db_name list = ["nocore"];
}

let core: hint_dataset = {
  name = "Core";
  positive_databases: hint_db_name list = ["core"];
  negative_databases: hint_db_name list = ["core"];
  decidability_databases: hint_db_name list = ["core"];
  shorten_databases: hint_db_name list = ["core"];
}

let algebra: hint_dataset = {
  name = "Algebra";
  positive_databases: hint_db_name list = ["wp_core"; "arith"; "wp_algebra"; "wp_classical_logic"; "wp_constructive_logic"; "wp_integers"; "zarith"];
  negative_databases: hint_db_name list = ["nocore"; "wp_negation_nat"; "wp_negation_int"];
  decidability_databases: hint_db_name list = ["nocore"; "wp_decidability_classical"; "wp_decidability_nat"];
  shorten_databases: hint_db_name list = ["wp_classical_logic"; "wp_constructive_logic"; "wp_core"];
}

let integers: hint_dataset = {
  name = "Integers";
  positive_databases: hint_db_name list = ["arith"; "zarith"; "wp_core"; "wp_classical_logic"; "wp_constructive_logic"; "wp_integers"];
  negative_databases: hint_db_name list = ["nocore"; "wp_decidability_nat"];
  decidability_databases: hint_db_name list = ["nocore"; "wp_negation_nat"; "wp_negation_int"];
  shorten_databases: hint_db_name list = ["wp_classical_logic"];
}

let reals_and_integers: hint_dataset = {
  name = "RealsAndIntegers";
  positive_databases: hint_db_name list = ["arith"; "zarith"; "real"; "wp_core"; "wp_classical_logic"; "wp_constructive_logic"; "wp_integers"; "wp_reals"; "wp_sets"];
  negative_databases: hint_db_name list = ["nocore"; "wp_negation_nat"; "wp_negation_int"; "wp_negation_reals"];
  decidability_databases: hint_db_name list = ["nocore"; "wp_decidability_nat"; "wp_decidability_reals"];
  shorten_databases: hint_db_name list = ["wp_sets"; "wp_classical_logic"];
}

let sets: hint_dataset = {
  name = "Sets";
  positive_databases: hint_db_name list = ["arith"; "zarith"; "wp_core"; "wp_classical_logic"; "wp_constructive_logic"; "wp_integers"];
  negative_databases: hint_db_name list = ["nocore"; "wp_decidability_nat"];
  decidability_databases: hint_db_name list = ["nocore"; "wp_negation_nat"; "wp_negation_int"];
  shorten_databases: hint_db_name list = ["wp_classical_logic"];
}