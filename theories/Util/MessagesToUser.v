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

Ltac2 @ external warn: message -> unit := "coq-waterproof" "warn_external".
Ltac2 @ external throw_external: message -> unit := "coq-waterproof" "throw_external".
Ltac2 @ external notice : message -> unit := "coq-waterproof" "notice_external".
Ltac2 @ external inform : message -> unit := "coq-waterproof" "inform_external".
Ltac2 @ external get_print_hypothesis_flag: unit -> bool := "coq-waterproof" "get_print_hypothesis_flag_external".
Ltac2 @ external get_redirect_errors_flag : unit -> bool := "coq-waterproof" "get_redirect_errors_flag_external".

Ltac2 Type exn ::= [RedirectedToUserError (message)].

Ltac2 throw (msg : message) :=
  if (get_redirect_errors_flag ()) then
    Control.zero (RedirectedToUserError msg)
  (** We use an OCaml error here, because it gets rendered much nicer in the editor *)
  else throw_external msg.
