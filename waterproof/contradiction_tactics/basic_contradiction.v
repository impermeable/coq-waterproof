(** * [basic_contradiction.v]
Author: 
    - Cosmin Manea (1298542)
Creation date: 09 June 2021

Two tactics: one for proving by contradiction, and one for finishing the proof after 
constructing a contradiction.
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
From Ltac2 Require Import Message.

Require Import Rbase.
Require Import Rfunctions.
Require Import SeqSeries.
Require Import Rtrigo.
Require Import Ranalysis.
Require Import Integration.
Require Import micromega.Lra.
Require Import Omega.
Require Import Max.
Require Import Classical.


(** * contra
    Starts a proof by contradiction.

    Arguments:
        - no arguments.

    Does:
        - starts a proof by contradiction.
*)
Ltac2 contra () :=
    lazy_match! goal with
        | [ |- ?x] => destruct (classic $x); try (assumption)
        | [ |- _] => print(of_string "Failed to start a proof by contradiction.")
    end.


(** * contradiction
    Calls the Ltac1 [contradiction] tactic.

    Arguments:
        - no arguments.

    Does:
        - calls the Ltac1 [contradiction] tactic, as this tactic does not exist in Ltac2.
*)
Ltac2 contradiction () :=
    ltac1:(contradiction).


Ltac2 Notation "We" "argue" "by" "contradiction" :=
  contra ().


Ltac2 Notation "Contradiction" :=
    contradiction ().