(**
  Type of exceptions used in Wateproof
*)
type wexn =
  | FailedBacktracing of string
  | NonExistingDataset of string

(**
  Throws an error with given info and message
*)
val throw : ?info:Exninfo.info -> wexn -> 'a
