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

(* Test 1: unfold term in goal, and throws an error suggesting 
  to remove the line after use. *)
Goal foo = 1.
Proof.
  Fail Expand the definition of foo.
Abort.

(* Test 2: unfold term in hypothese and goal, and throws an error suggesting 
    to remove the line after use. *)
Goal (foo = 0) -> (foo = 2) -> (foo = 1).
Proof.
  intros.
  Fail Expand the definition of foo.
Abort.

(* Test 3: fails to unfold term if it does not occur in any statement. *)
Goal False.
Proof.
  Fail Expand the definition of foo.
Abort.



(* Tests framework expand the definition. *)
Local Ltac2 unfold_foo (statement : constr) := eval unfold foo in $statement.
Ltac2 Notation "Expand" "the" "definition" "of" "foo2" := 
  panic_if_goal_wrapped ();
  unfold_in_all unfold_foo (Some "foo2") true.

(* Test 4: unfold term in hypotheses and goal and throws an error suggesting 
    to remove line after use. *)
Goal (foo = 0) -> (foo = 2) -> (foo = 1).
Proof.
  intros.
  Fail Expand the definition of foo2.
Abort.

(* Test 5: fails to unfold term in statment without term. *)
Goal False.
Proof.
  Fail Expand the definition of foo2.
Abort.


(** Check unfolding method that does not throw an error.
  Meant for internal use by custom Waterproof editor. *)

(** Non-framework version. *)

(* Test 6: unfold term in hypotheses and goal without throwing an error. *)
Goal (foo = 0) -> (foo = 2) -> (foo = 1).
Proof.
  intros.
  _internal_ Expand the definition of foo.
Abort.

(* Test 7: unfold fails to unfold term if no statement with term. *)
Goal False.
Proof.
  _internal_ Expand the definition of foo.
Abort.

(* Test 8: outdated format (for format used by Waterproof editor, for now) *)
Goal (foo = 0) -> (foo = 2) -> (foo = 1).
Proof.
  intros.
  _internal_ Expand the definition of foo in ().
Abort.
    
(** Framework version:  *)
  
Ltac2 Notation "_internal_" "Expand" "the" "definition" "of" "foo2" x(opt(seq("in", "()"))) :=
  panic_if_goal_wrapped (); 
  unfold_in_all unfold_foo (Some "foo2") false.

(* Test 9: unfold term in hypotheses and goals. *)
Goal (foo = 0) -> (foo = 2) -> (foo = 1).
Proof.
  intros.
  _internal_ Expand the definition of foo2.
Abort.

(* Test 10: fails to unfold term if no statements with term. *)
Goal False.
Proof.
   _internal_ Expand the definition of foo2.
Abort.

(* Test 11: outdated format (for format used by Waterproof editor, for now) *)
Goal (foo = 0) -> (foo = 2) -> (foo = 1).
Proof.
  intros.
  _internal_ Expand the definition of foo2 in ().
Abort.
