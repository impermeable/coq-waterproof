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
Require Import Ltac2.Message.

Require Import Waterproof.Waterproof.
Require Import Waterproof.Automation.
Require Import Waterproof.Tactics.
Require Import Waterproof.Util.Assertions.

Definition foo : nat := 0.

(* Tests general unfolding: *)

(* Test 1: unfold term in statement and throws an error suggesting 
    to remove line to continue. *)
Goal False.
Proof.
  Fail Expand the definition of foo in foo.
Abort.

(* Test 2: unfold term in statement matching goal, and throws an error suggesting 
  to replace line with 'We need to show that ...'. *)
Goal foo = 1.
Proof.
  Fail Expand the definition of foo in (foo = 1).
Abort.

(* Test 3: unfold term in statement matching a hypothesis and throws an error suggesting 
    to replace line with 'It holds that ...'. *)
Goal (foo = 0) -> (foo = 2) -> (foo = 1).
Proof.
  intros.
  Fail Expand the definition of foo in (foo = 0).
  Fail Expand the definition of foo in (foo = 2).
Abort.

(* Test 4: fails to unfold term in statment without term. *)
Goal False.
Proof.
  Fail Expand the definition of foo in 0.
Abort.



(* Tests framework expand the definition. *)
Local Ltac2 unfold_foo (statement : constr) := eval unfold foo in $statement.
Ltac2 Notation "Expand" "the" "definition" "of" "foo2" "in" statement(constr) := 
  unfold_in_statement unfold_foo (Some "foo2") statement.

(* Test 5: unfold term in statement and throws an error suggesting 
    to remove line to continue. *)
Goal False.
Proof.
  Fail Expand the definition of foo2 in foo.
Abort.

(* Test 6: unfold term in statement matching goal, and throws an error suggesting 
    to replace line with 'We need to show that ...'. *)
Goal foo = 1.
Proof.
  Fail Expand the definition of foo2 in (foo = 1).
Abort.

(* Test 7: unfold term in statement matching a hypothesis and throws an error suggesting 
    to replace line with 'It holds that ...'. *)
Goal (foo = 0) -> (foo = 2) -> (foo = 1).
Proof.
  intros.
  Fail Expand the definition of foo2 in (foo = 0).
  Fail Expand the definition of foo2 in (foo = 2).
Abort.

(* Test 8: fails to unfold term in statment without term. *)
Goal False.
Proof.
  Fail Expand the definition of foo2 in 0.
Abort.


(** Check unfolding method that does not throw an error.
  Meant for internal use by custom Waterproof editor. *)
Ltac2 Notation "_internal_" "Expand" "the" "definition" "of" "foo2" "in" statement(constr) := 
  unfold_in_statement_no_error unfold_foo (Some "foo2") statement.

(* Test 9: unfold term in statement. *)
Goal False.
Proof.
  _internal_ Expand the definition of foo2 in foo.
Abort.

(* Test 10: unfold term in statement matching goal, and prints a message suggesting 
    to replace line with 'We need to show that ...'. *)
Goal foo = 1.
Proof.
  _internal_ Expand the definition of foo2 in (foo = 1).
Abort.

(* Test 11: unfold term in statement matching a hypothesis and prints a message suggesting 
    to replace line with 'It holds that ...'. *)
Goal (foo = 0) -> (foo = 2) -> (foo = 1).
Proof.
  intros.
  _internal_ Expand the definition of foo2 in (foo = 0).
  _internal_ Expand the definition of foo2 in (foo = 2).
Abort.

(* Test 12: fails to unfold term in statment without term. *)
Goal False.
Proof.
   _internal_ Expand the definition of foo2 in 0.
Abort.

(* Test 13: internal unfold term in statement and throws an error suggesting 
    to remove line to continue. *)
Goal False.
Proof.
  _internal_ Expand the definition of foo in foo.
Abort.

(* Test 14: internal unfold term in statement matching goal, and throws an error suggesting 
  to replace line with 'We need to show that ...'. *)
Goal foo = 1.
Proof.
  _internal_ Expand the definition of foo in (foo = 1).
Abort.

(* Test 15: internal unfold term in statement matching a hypothesis and throws an error suggesting 
    to replace line with 'It holds that ...'. *)
Goal (foo = 0) -> (foo = 2) -> (foo = 1).
Proof.
  intros.
  _internal_ Expand the definition of foo in (foo = 0).
  _internal_ Expand the definition of foo in (foo = 2).
Abort.

(* Test 16: internal unfold fails to unfold term in statment without term. *)
Goal False.
Proof.
  _internal_ Expand the definition of foo in 0.
Abort.
