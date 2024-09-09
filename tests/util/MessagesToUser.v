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

Lemma test : 0 = 0.
Proof.
  warn (Message.of_string "This warning _should_ be printed.").
  Fail throw (Message.of_string "This error _should_ be raised.").
Abort.

(** Test whether enabling the hypothesis flag works.
*)
Waterproof Enable Hypothesis Help.

Goal False.
assert_is_true (get_print_hypothesis_flag ()).
Abort.

(** Test whether disabling the hypothesis flag works.
*)
Waterproof Disable Hypothesis Help.

Goal False.
assert_is_false (get_print_hypothesis_flag ()).
Abort.
