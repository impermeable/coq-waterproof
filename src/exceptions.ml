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

open Pp

(**
  Basic exception info
*)
let fatal_flag: 'a Exninfo.t = Exninfo.make ()

(**
  Type of exceptions used in Wateproof
*)
type wexn =
  | CastError of string (** Indicates that a cast made by the FFI has failed  *)
  | FailedAutomation of string (** Indicates that the automatic solver called has failed  *)
  | FailedTest of string (** Indicates that the running test has failed *)
  | NonExistingDataset of Hints.hint_db_name (** Indicates that the user tried to import a non-existing hint dataset *)
  | UnusedLemmas (** Indicates that no proof using all the given lemmas has been found *)
  | ToUserError of Pp.t (** An error that should go directly to the user *)

(**
  Converts errors to displayable messages
*)
let pr_wexn (exn: wexn): t =
  match exn with
    | CastError message -> str "Cast error: " ++ str message
    | FailedAutomation message -> str "Automatic solving failed: " ++ str message
    | FailedTest test -> str "Failed test: " ++ str test
    | NonExistingDataset dataset -> str "Non existing dataset: the dataset " ++ str dataset ++ str " is not defined"
    | UnusedLemmas -> str "No proof using all given lemmas has been found"
    | ToUserError message -> message

(**
  Throws an error with given info and message
*)
let throw ?(info: Exninfo.info = Exninfo.null) (exn: wexn): 'a =
  let fatal = Exninfo.add info fatal_flag () in
  CErrors.user_err ?info:(Some fatal) (pr_wexn exn)

(** 
  Sends a warning and returns the message as a string
*)
let warn (input : Pp.t) : unit Proofview.tactic = 
  Proofview.tclUNIT @@ Feedback.msg_warning input

(**
  Throws an error
*)
let err (input : Pp.t) : unit Proofview.tactic =
  Proofview.tclUNIT @@ throw (ToUserError input)
