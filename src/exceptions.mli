(**
  Type of exceptions used in Wateproof
*)
type wexn =
  | FailedAutomation of string (** Indicates that the automatic solver called has failed  *)
  | FailedTest of string (** Indicates that the running test has failed *)
  | NonExistingDataset of Hints.hint_db_name (** Indicates that the user tried to import a non-existing hint dataset *)
  | UnusedLemmas (** Indicates that no proof using all the given lemmas has been found *)

(**
  Throws an error with given info and message
*)
val throw : ?info:Exninfo.info -> wexn -> 'a
