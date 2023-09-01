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

Require Export Util.Goals.
Require Import Util.MessagesToUser.


(**
  Split the proof of an if and only if statement into both of its directions, wraps both resulting goals in a [StateGoal.Wrapper].

  Arguments:
    - no arguments

  Does:
    - splits the if and only if statement into its both directions.
    - wraps both goals in a [StateGoal.Wrapper].

  Raises fatal exceptions:
    - If the [goal] is not an if and only if [goal].
*)
Ltac2 both_statements_iff () :=
  lazy_match! goal with 
    | [ |- _ <-> _] => split; Control.enter (fun () => apply StateGoal.unwrap)
    | [ |- _ ] => throw (Message.of_string "The goal is not to show an `if and only if`-statement, try another approach.")
  end.

Ltac2 Notation "We" "show" "both" "directions" := 
  panic_if_goal_wrapped ();
  both_statements_iff ().

Ltac2 Notation "We" "prove" "both" "directions" := 
  panic_if_goal_wrapped ();
  both_statements_iff ().
