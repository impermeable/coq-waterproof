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
Require Import Waterproof.Util.Assertions.

Ltac2 @ external warn: message -> unit := "coq-waterproof" "warn_external".
Ltac2 @ external throw: message -> unit := "coq-waterproof" "throw_external".
Ltac2 @ external get_print_hypothesis_flag: unit -> bool := "coq-waterproof" "get_print_hypothesis_flag_external".
Ltac2 @ external get_last_warning : unit -> message option := "coq-waterproof" "get_last_warning_external".
Ltac2 @ external catch_error_message : (unit -> 'a) -> message option := "coq-waterproof" "catch_error_return_message_external".

Ltac2 assert_warning_equals_string (str : string) :=
  match get_last_warning () with
  | Some msg => assert_is_true (String.equal (Message.to_string msg) str)
  | None => throw (Message.of_string "No warning was raised.")
  end.
