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

Require Export Ltac2.Ltac2.
Require Import Ltac2.Bool.
Require Import Ltac2.Init.
Require Import Ltac2.String.

Require Import Waterproof.Waterproof.

(** TODO: in later versions of Coq this can be replaced by a native function *)
Ltac2 fnl () := Message.of_string "
".

Local Ltac2 Type feedback_lvl_ffi.

Ltac2 @ external feedback_lvl_debug_ffi : unit -> feedback_lvl_ffi := "coq-core.plugins.coq-waterproof" "feedback_lvl_debug".
Ltac2 @ external feedback_lvl_info_ffi : unit -> feedback_lvl_ffi := "coq-core.plugins.coq-waterproof" "feedback_lvl_info".
Ltac2 @ external feedback_lvl_notice_ffi : unit -> feedback_lvl_ffi := "coq-core.plugins.coq-waterproof" "feedback_lvl_notice".
Ltac2 @ external feedback_lvl_warning_ffi : unit -> feedback_lvl_ffi := "coq-core.plugins.coq-waterproof" "feedback_lvl_warning".
Ltac2 @ external feedback_lvl_error_ffi : unit -> feedback_lvl_ffi := "coq-core.plugins.coq-waterproof" "feedback_lvl_error".

Ltac2 @ external send_message_external: feedback_lvl_ffi -> message -> unit := "coq-core.plugins.coq-waterproof" "message_external".
Ltac2 @ external throw_external: message -> unit := "coq-core.plugins.coq-waterproof" "throw_external".
Ltac2 @ external get_print_hypothesis_flag: unit -> bool := "coq-core.plugins.coq-waterproof" "get_print_hypothesis_flag_external".
Ltac2 @ external get_redirect_errors_flag : unit -> bool := "coq-core.plugins.coq-waterproof" "get_redirect_errors_flag_external".

Ltac2 @ external get_last_warning : unit -> message option :=
  "coq-core.plugins.coq-waterproof" "get_last_warning_external".
Ltac2 @ external get_feedback_log_external : feedback_lvl_ffi -> message list :=
  "coq-core.plugins.coq-waterproof" "get_feedback_log_external".

Ltac2 Type FeedbackLevel := [ Debug | Info | Notice | Warning | Error ].

Ltac2 feedback_lvl_to_ffi (lvl : FeedbackLevel) :=
  match lvl with
  | Debug => feedback_lvl_debug_ffi ()
  | Info => feedback_lvl_info_ffi ()
  | Notice => feedback_lvl_notice_ffi ()
  | Warning => feedback_lvl_warning_ffi ()
  | Error => feedback_lvl_error_ffi ()
  end.

Ltac2 Type exn ::= [RedirectedToUserError (message)].

Ltac2 send_message (lvl : FeedbackLevel) (msg : message) :=
  send_message_external (feedback_lvl_to_ffi lvl) msg.

Ltac2 inform (msg : message) :=
  send_message Info msg.

Ltac2 notice (msg : message) :=
  send_message Notice msg.

Ltac2 warn (msg : message) :=
  send_message Warning msg.

Ltac2 get_feedback_log (lvl : FeedbackLevel) :=
  get_feedback_log_external (feedback_lvl_to_ffi lvl).

Ltac2 info_notice (msg : message) := inform msg; notice msg.
  (* We send both here because with the right settings in coq-waterproof,
     they show up in different places in the editor. *)

Ltac2 replace_notice (template : string) := 
  notice (Message.concat (Message.of_string "Hint, replace with: ") (Message.of_string template)).

(* We slightly abuse the levels here: notice shows up inline and has special treatment to
   work with the templates, inform shows up in the sidebar. *)
Ltac2 insert_msg (msg : string) (template : string) := 
  inform (Message.concat (Message.of_string "Hint, insert: ") (Message.of_string msg));
  notice (Message.concat (Message.of_string "Hint, insert: ") (Message.of_string template)).

Ltac2 replace_msg (msg : string) (template : string) := 
  inform (Message.concat (Message.of_string "Hint, replace with: ") (Message.of_string msg));
  replace_notice template.

(* Note, there could arise a use case for sending an error on the feedback channel without
  actually raising an error, but it could also be confusing. For now, errors are therefore
  handled through a different channel *)
Ltac2 throw (msg : message) :=
  if (get_redirect_errors_flag ()) then
    Control.zero (RedirectedToUserError msg)
  (** We use an OCaml error here, because it gets rendered much nicer in the editor *)
  else throw_external msg.
