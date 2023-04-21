val loaded_hint_database_names : Hints.hint_db_name list Summary.Local.local_ref

val load_database : Hints.hint_db_name -> unit

val unload_database : Hints.hint_db_name -> unit

module type HintDataset = sig
  val name : string
  val positive_databases : string list
  val negative_databases : string list
  val decidability_databases : string list
  val shorten_databases : string list
end

val load_dataset : (module HintDataset) -> unit

module Core: HintDataset
module Algebra : HintDataset
module RealsAndIntegers : HintDataset
module Integers : HintDataset
module Sets : HintDataset