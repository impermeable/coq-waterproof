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

Require Import Ltac2.Ltac2.
Require Import Waterproof.Waterproof.
Require Import Waterproof.Util.MessagesToUser.
Require Import Waterproof.Util.Assertions.

(* Waterproof Enable Redirect Warnings. *)

Waterproof Enable Redirect Warnings.
Waterproof Enable Redirect Errors.

(** * Tests of the test framework *)

(** ** Test for a warning *)
Goal True.
assert_warns_with_string (fun () => warn (Message.of_string "Send a first warning.")) "Send a first warning.".
Abort.

(** ** Test if a warning is really thrown (and not just the last item in the log is compared) *)
Goal True.
warn (Message.of_string "Send a warning.").
Fail assert_warns_with_string (fun () => ()) "Send a warning.".
Abort.

(** ** Test asserting for a failure with a given string *)
Goal True.
assert_fails_with_string (fun () => throw (Message.of_string "This error _should_ be raised.")) "This error _should_ be raised.".
Abort.

(** ** Test of the error message of the assert_fails_with_string tactic itself *)
Goal True.
assert_fails_with_string
  (fun () => assert_fails_with_string (fun () => throw (Message.of_string "foo")) "bar")
"The tactic failed, but with an unexpected error message. Expected:
bar
Got:
foo".
Abort.

(** ** Test of the error message of the assert_warns_with_string tactic *)
Goal True.
assert_fails_with_string
  (fun () => assert_warns_with_string (fun () => warn (Message.of_string "foo")) "bar")
"The tactic warned, but with an unexpected error message. Expected:
bar
Got:
foo".
Abort.

Goal True.
assert_warns_with_string (fun () => warn (Message.of_string "warning
with line break")) "warning
with line break".
Abort.

Goal True.
assert_warns_with_strings (fun () =>
  warn (Message.of_string "first warning");
  warn (Message.of_string "second warning"))
["first warning"; "second warning"].
Abort.