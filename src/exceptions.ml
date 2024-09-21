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
open Feedback

let wp_debug_log = Summary.ref ~name:"wp_debug_log" []
let wp_info_log = Summary.ref ~name:"wp_info_log" []
let wp_notice_log = Summary.ref ~name:"wp_notice_log" []
let wp_warning_log = Summary.ref ~name:"wp_warning_log" []
let wp_error_log = Summary.ref ~name:"wp_error_log" []

(**
  A rudimentary feedback log
*)
let feedback_log (lvl : level) : Pp.t list ref =
  match lvl with
  | Debug -> wp_debug_log
  | Info -> wp_info_log
  | Notice -> wp_notice_log
  | Warning -> wp_warning_log
  | Error -> wp_error_log

(**
  The id that we obtained when registering wp_feedback_logger as a feeder in Feedback.mli
*)
let wp_feedback_logger_id = Summary.ref ~name: "wp_feedback_logger_id" None

let info_counter = Summary.ref ~name:"info_counter" 0

(**
  A custom feedback logger for waterproof
*)
let wp_feedback_logger (fb : feedback) : unit =
  match fb.contents with
  | Message (lvl, _, msg) ->
    (feedback_log lvl :=
      (msg) :: !(feedback_log lvl);
    info_counter := !info_counter + 1)
  | _ -> ()

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
let redirect_feedback : bool ref = Summary.ref ~name:"redirect_feedback" false

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
  Send a message
*)
let message (lvl : Feedback.level) (input : Pp.t) : unit Proofview.tactic =
  if !redirect_feedback then
    Proofview.tclUNIT @@ (feedback_log lvl := input :: !(feedback_log lvl))
  else
    Proofview.tclUNIT @@ feedback (Message (lvl, None, input))

(**
  Send a warning
*)
let warn (input : Pp.t) : unit Proofview.tactic =
  message Warning input

(**
  Send a notice
*)
let notice (input : Pp.t) : unit Proofview.tactic =
  message Notice input

(**
  Send an info message
*)
let inform (input : Pp.t) : unit Proofview.tactic =
  message Info input

(**
  Throw an error
*)
let err (input : Pp.t) : unit Proofview.tactic =
  throw (ToUserError input)

(**
  Return the last warning
*)
let get_last_warning () : Pp.t option Proofview.tactic =
  Proofview.tclUNIT @@
    match !(feedback_log Warning) with
    | [] -> None
    | hd :: tl -> Some hd
