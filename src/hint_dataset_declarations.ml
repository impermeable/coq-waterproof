open Hints

(**
  Interface to load and unload usual hint databases such as reals, integers, classical logic, ...
*)
type hint_dataset = {
  
  (*
    Dataset name
  *)
  name: string;

  (*
    Databases that will be called to solve a goal
  *)
  positive_databases: hint_db_name list;
  
  (*
    Databases that will be called to solve a goal containing a negation
  *)
  negative_databases: hint_db_name list;

  (*
    Databases that can be called to solve a goal with decidability properties
  *)
  decidability_databases: hint_db_name list;

  (*
    Databases that will be called to solve a goal faster than [positive_databases]
  *)
  shorten_databases: hint_db_name list;
}

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
  positive_databases: hint_db_name list = ["arith"; "wp_algebra"; "wp_classical_logic"; "wp_constructive_logic"; "wp_integers"; "zarith"];
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