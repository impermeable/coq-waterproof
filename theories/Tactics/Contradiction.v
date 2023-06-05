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

Require Import Classical.
Require Import Ltac2.Ltac2.
Require Import Ltac2.Message.

Require Import Waterproof.Util.Goals.

(**
  Starts a proof by contradiction.

  Arguments:
    - no arguments.

  Does:
    - Replaces the goal [G] by its double negation [¬ ¬ G].
*)
Ltac2 contra () :=
  lazy_match! goal with
    | [ |- ?x] =>
      apply (NNPP $x);
      apply (ByContradiction.unwrap (not $x))
    | [ |- _] => print(of_string "Failed to start a proof by contradiction.")
  end.


(**
  Calls the Ltac1 [contradiction] tactic.

  Arguments:
    - no arguments.

  Does:
    - calls the Ltac1 [contradiction] tactic, as this tactic does not exist in Ltac2. Tries to find contradictory hypotheses to show the goal.
*)
Ltac2 contradiction () := ltac1:(contradiction).

Ltac2 Notation "We" "argue" "by" "contradiction" := contra ().

Ltac2 Notation "Contradiction" := contradiction ().

Ltac2 Notation "↯" := contradiction ().