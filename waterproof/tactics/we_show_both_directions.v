(** * [we_show_both_directions.v]
Authors: 
    - Cosmin Manea (1298542)
    - Jelle Wemmenhove
Creation date: 22 May 2021

Version of [We show/prove both directions] tactic.
[We show/prove both directions] can be used to split the proof of an if and only if statement.

--------------------------------------------------------------------------------

This file is part of Waterproof-lib.

Waterproof-lib is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

Waterproof-lib is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with Waterproof-lib.  If not, see <https://www.gnu.org/licenses/>.
*)

From Ltac2 Require Import Ltac2.

Require Export Waterproof.debug.
Require Export Waterproof.tactics.goal_wrappers.
Require Export Waterproof.tactics.we_need_to_show. (* Enable the unwrapping of the StateGoal wrapper *)

Ltac2 Type exn ::= [ BothDirectionsError(string) ].

Ltac2 raise_both_directions_error (s:string) := 
    Control.zero (BothDirectionsError s).

(** * both_statements_iff
    Split the proof of an if and only if statement into both of its directions, 
    wraps both resulting goals in a [StateGoal.Wrapper].

    Arguments:
        - no arguments

    Does:
        - splits the if and only if statement into its both directions.
        - wraps both goals in a [StateGoal.Wrapper].

    Raises Exceptions:
        - [BothDirectionsError], if the [goal] is not an if and only if [goal].
*)
Ltac2 both_statements_iff () :=
    lazy_match! goal with 
        | [ |- _ <-> _] => split; Control.enter (fun () => apply StateGoal.unwrap)
        | [ |- _ ] => raise_both_directions_error("The goal is not to show an ‘if and only if’-statement,
try another tactic.")
    end.


Ltac2 Notation "We" "show" "both" "directions" := 
  debug "both_directions" "start";
  panic_if_goal_wrapped ();
  both_statements_iff ().

Ltac2 Notation "We" "prove" "both" "directions" := 
  debug "both_directions" "start";
  panic_if_goal_wrapped ();
  both_statements_iff ().