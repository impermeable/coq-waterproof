open Hints
open Summary

open Exceptions
open Hint_dataset_declarations

(**
  Contains the hint dataset that is currently loaded
*)
let loaded_hint_dataset: string ref = ref ~name:"loaded_hint_dataset" (name core)

(**
  Complete list of all existing dataset names
*)
let existing_dataset_names: string list = ["Empty"; "Core"; "Algebra"; "Integers"; "RealsAndIntegers"; "Sets"]

(**
  Replace all current loaded hints by the ones declared in the [hint_dataset]
*)
let load_dataset (hint_dataset_name: string): unit =
  if List.mem hint_dataset_name existing_dataset_names then
    loaded_hint_dataset := hint_dataset_name
  else
    throw (NonExistingDataset hint_dataset_name)

(**
  Converts a name into the corresponding hint dataset
*)
let dataset_of_name (name: string): hint_dataset = 
  match name with
    | "Empty" -> empty
    | "Core" -> core
    | "Integers" -> integers
    | "RealsAndIntegers" -> reals_and_integers
    | "Sets" -> sets
    | _ -> throw (NonExistingDataset name)

(**
  Returns the list of databases of the current loaded dataset for the given {! Hint_dataset_declarations.database_type}
*)
let get_current_databases (database_type: database_type): hint_db_name list =
  get_databases (dataset_of_name !loaded_hint_dataset) database_type