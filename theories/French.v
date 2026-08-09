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

(** French entry point for the Waterproof tactic language.

    Import this module instead of [Waterproof.Tactics] to use the French tactic
    keywords and French user-facing messages:

    <<
      Require Import Waterproof.French.
    >>

    For every tactic file whose notations have been split into [English]/[French]
    submodules, this file exports the [French] submodule (so the French keywords
    are the active ones, mutually exclusive with the English ones). Tactic files
    that have not been translated yet still expose their English notations; they
    are exported here unchanged until a French translation is available. *)

Require Export Ltac2.Ltac2.

(** Language-neutral content that the English entry point re-exports too
    (goal wrappers, the [Case]/[Cas] tactic, ...). Safe to export: it contains
    no language-specific tactic notations. *)
Require Export Util.Goals.

Require Tactics.Assume.
Require Tactics.Because.
Require Tactics.BothDirections.
Require Tactics.BothStatements.
Require Tactics.Claims.
Require Tactics.Choose.
Require Tactics.Obtain.
Require Tactics.Conclusion.
Require Tactics.Contradiction.
Require Tactics.Define.
Require Tactics.Either.
Require Tactics.Help.
Require Tactics.Induction.
Require Tactics.ItHolds.
Require Tactics.ItSuffices.
Require Tactics.Specialize.
Require Tactics.Take.
Require Tactics.ToShow.
Require Tactics.Unfold.
Require Tactics.By.

(** Activate the French notations for the translated tactic files.
    (English notations of these files are deliberately NOT exported here.) *)
Export Assume.French.
Export Because.French.
Export BothDirections.French.
Export BothStatements.French.
Export Choose.French.
Export Obtain.French.
Export Conclusion.French.
Export Contradiction.French.
Export Define.French.
Export Either.French.
Export Help.French.
Export Induction.French.
Export ItHolds.French.
Export ItSuffices.French.
Export Specialize.French.
Export Take.French.
Export ToShow.French.
Export Unfold.French.
Export By.French.
Export Claims.French.

(** Switch user-facing messages to French.
    NB: the [Waterproof Language] command sets a flag that is local to the file
    in which it is issued; it does not propagate through [Require Import]. Users
    of this module that want French messages should therefore also write
    [Waterproof Language French.] at the top of their own file. *)
Waterproof Language French.
