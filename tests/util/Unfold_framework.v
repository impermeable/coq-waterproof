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
Require Import Waterproof.Tactics.Unfold.
Require Import Waterproof.Util.MessagesToUser.
Require Import Waterproof.Util.Assertions.

(* Test 1 : Register a simple notation and use it to expand a definition *)

Local Definition z := 2.

Waterproof Register Unfold "test1" "unfold" "phrase" z.

Goal z = 2.
Unfold the definition of test1 unfold phrase.
assert_is_true (Constr.equal (Control.goal ()) constr:(2 = 2)).
reflexivity.
Abort.

(* TODO: add a test for expanding a definition that is defined
in a different module with the framework *)