open Pp

(**
  Basic exception info
*)
let fatal_flag: 'a Exninfo.t = Exninfo.make ()

(**
  Type of exceptions used in Wateproof
*)
type wexn = 
  | FailedBacktracing of string (** Indicates that the backtracking has failed *)
  | NonExistingDataset of string (** Indicates that the user tried to import a non-existing hint dataset *)
  | UnusedLemma of string list (** Indicates that a given lemma has not been used during automatic solving *)

(**
  Converts 
*)
let pr_wexn (exn: wexn): t =
  match exn with
    | FailedBacktracing message -> str "Backtracking failed: " ++ str message
    | NonExistingDataset dataset -> str "Non existing dataset: the dataset " ++ str dataset ++ str " is not defined"
    | UnusedLemma lemma_names -> str "Unused lemma(s): the given lemma(s)" ++ (List.fold_left (fun acc name -> acc ++ str " " ++ str name) (str "") lemma_names) ++ str " was/were not used during the automatic solving"

(**
  Throws an error with given info and message
*)
let throw ?(info: Exninfo.info = Exninfo.null) (exn: wexn): 'a =
  let fatal = Exninfo.add info fatal_flag () in
  CErrors.user_err ?info:(Some fatal) (pr_wexn exn)