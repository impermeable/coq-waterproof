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
open Proofview
open Proofview.Notations
open Feedback

(**
  A rudimentary feedback log
*)
let feedback_log : Pp.t list ref = Summary.ref ~name:"feedback_log" []

(**
  The id that we obtained when registering wp_feedback_logger as a feeder in Feedback.mli
*)
let wp_feedback_logger_id = Summary.ref ~name: "wp_feedback_logger_id" None

(**
  A custom feedback logger for waterproof
*)
let wp_feedback_logger (fb : feedback) : unit =
  match fb.contents with
  | Message (_, _, msg) ->
    feedback_log := msg :: !feedback_log
  | _ -> ()

(** 
  Print the full log
*)
let print_feedback_log () : unit Proofview.tactic =
  tclUNIT @@ List.iter (fun msg -> msg_notice msg) !feedback_log

(**
  Adds wp_feedback_logger to Coq's feedback mechanism
*)
let add_wp_feedback_logger () : unit =
  match !wp_feedback_logger_id with
  | Some _ -> msg_warning (str "The waterproof feedback logger was already added")
  | None -> let id = Feedback.add_feeder wp_feedback_logger in
            wp_feedback_logger_id := Some id

(**
  Basic exception info
*)
let fatal_flag: 'a Exninfo.t = Exninfo.make ()

(**
  The last thrown warning
*)
let last_thrown_warning : Pp.t option ref = Summary.ref ~name:"last_thrown_warning" None

(**
  Redirect warnings: this is useful when testing the plugin
*)
let redirect_warnings : bool ref = Summary.ref ~name:"redirect_warnings" false

(**
  Redirect errors: this is useful when testing the plugin
*)
let redirect_errors : bool ref = Summary.ref ~name:"redirect_errors" false

(**
  Print hypotheses help
*)
let print_hypothesis_help : bool ref = Summary.ref ~name:"print_hypothesis_help" false

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
  Sends a warning
*)
let warn (input : Pp.t) : unit Proofview.tactic =
  if !redirect_warnings then 
    Proofview.tclUNIT @@ (feedback_log := input :: !feedback_log)
  else
    Proofview.tclUNIT @@ msg_warning input

(** 
  Sends a notice
*)
let notice (input : Pp.t) : unit Proofview.tactic =
  Proofview.tclUNIT @@ msg_notice input

(**
  Send an info message
*)
let inform (input : Pp.t) : unit Proofview.tactic =
  Proofview.tclUNIT @@ msg_info input

let warn' (input : Pp.t) ?(proc = Feedback.msg_warning) : unit Proofview.tactic =
  Proofview.tclUNIT @@ proc input
(**
  Throws an error
*)
let err (input : Pp.t) : unit Proofview.tactic =
  (* Route the message to our own logger. Note that we need to follow
     the feedback mechanism otherwise the message does not arrive in the log *)
  throw (ToUserError input)

(**
  Return the last warning
*)
let get_last_warning () : Pp.t option Proofview.tactic =
  Proofview.tclUNIT @@
    match !feedback_log with
    | [] -> None
    | hd :: tl -> Some hd
