open Pp

(**
  Basic exception info
*)
let fatal_flag: 'a Exninfo.t = Exninfo.make ()

(**
  Type of exceptions used in Wateproof
*)
type wexn = 
  
  (*
    Indicates that the user tried to import a non-existing hint dataset
  *)
  | NonExistingDataset of string

(**
  Converts 
*)
let pr_wexn (exn: wexn): t =
  match exn with
    | NonExistingDataset dataset -> str "Non existing dataset: the dataset " ++ str dataset ++ str " is not defined"

(**
  Throws an error with given info and message
*)
let throw ?(info: Exninfo.info = Exninfo.null) (exn: wexn): 'a =
  let fatal = Exninfo.add info fatal_flag () in
  CErrors.user_err ?info:(Some fatal) (pr_wexn exn)