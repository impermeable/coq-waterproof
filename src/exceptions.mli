(**
  Type of exceptions used in Wateproof
*)
type wexn = 
  | FailedBacktracing of string (** Indicates that the backtracking has failed *)
  | NonExistingDataset of string (** Indicates that the user tried to import a non-existing hint dataset *)
  | UnusedLemma of string list (** Indicates that a given lemma has not been used during automatic solving *)

(**
  Throws an error with given info and message
*)
val throw : ?info:Exninfo.info -> wexn -> 'a
