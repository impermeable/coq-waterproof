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

Require Export Tactics.Assume.
Require Export Tactics.Because.
Require Export Tactics.BothDirections.
Require Export Tactics.BothStatements.
Require Export Tactics.Claims.
Require Export Tactics.Choose.
Require Export Tactics.Obtain.
Require Export Tactics.Conclusion.
Require Export Tactics.Contradiction.
Require Export Tactics.Define.
Require Export Tactics.Either.
Require Export Tactics.Help.
Require Export Tactics.Induction.
Require Export Tactics.ItHolds.
Require Export Tactics.ItSuffices.
Require Export Tactics.Specialize.
Require Export Tactics.Take.
Require Export Tactics.ToShow.
Require Export Tactics.Unfold.
Require Export Tactics.By.

(** Activate the French notations for the translated tactic files.
    (English notations of these files are deliberately NOT exported here.) *)
Export Conclusion.French.

(** Switch user-facing messages to French.
    NB: the [Waterproof Language] command sets a flag that is local to the file
    in which it is issued; it does not propagate through [Require Import]. Users
    of this module that want French messages should therefore also write
    [Waterproof Language French.] at the top of their own file. *)
Waterproof Language French.
