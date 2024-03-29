(******************************************************************************)
(*                  This file is part of Waterproof-lib.                      *)
(*                                                                            *)
(*   Waterproof-lib is free software: you can redistribute it and/or modify   *)
(*    it under the terms of the GNU General Public License as published by    *)
(*     the Free Software Foundation, either version 3 of the License, or      *)
(*                    (at your option) any later version.                     *)
(*                                                                            *)
(*     Waterproof-lib is distributed in the hope that it will be useful,      *)
(*      but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*       MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the         *)
(*               GNU General Public License for more details.                 *)
(*                                                                            *)
(*     You should have received a copy of the GNU General Public License      *)
(*   along with Waterproof-lib. If not, see <https://www.gnu.org/licenses/>.  *)
(*                                                                            *)
(******************************************************************************)

(**
  Contains the hint dataset that is currently loaded
*)
val loaded_hint_dataset : string list ref

(**
  Dictionary with dataset names as keys and datasets as values
*)
val existing_datasets: Hint_dataset_declarations.hint_dataset Proofutils.StringMap.t ref

(**
  Replace all current loaded hints by the ones declared in the [hint_dataset]
*)
val load_dataset : string -> unit

(**
  Removes a dataset to the currently loaded hint datasets
*)
val remove_dataset : string -> unit

(**
  Clears all the currently loaded datasets
*)
val clear_dataset : unit -> unit

(**
  Creates a new empty dataset from a given name
*)
val create_new_dataset: string -> unit

(**
  Sets the databases of a given {! database_type} in a given dataset
*)
val populate_dataset :
  string ->
  Hint_dataset_declarations.database_type ->
  string list ->
  unit

(**
  Returns the list of databases of the current loaded dataset for the given {! Hint_dataset_declarations.database_type}
*)
val get_current_databases : Hint_dataset_declarations.database_type -> Hints.hint_db_name list