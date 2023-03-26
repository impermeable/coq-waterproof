(** * [databases.v]

Authors: 
    - Adrian Vramulet (1284487)
    - Tudor Voicu (1339532)
    - Lulof Pirée (1363638)
    - Cosmin Manea (1298542)
Creation date: 14 June 2021

In this file, we construct so-called Hint Databases.
These databases can be used in combination with the tactics 
`auto` and `eauto`.
When using such a tactic, 
the hints in the database are recursively called 
until a certain search depth (standard is 5).
We choose to split the interesting hints among a number 
of different databases, so that the recursive search
size and the corresponding search time remain relatively small.

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


Require Import Coq.Logic.PropExtensionality.
Require Import Waterproof.definitions.set_definitions.
Require Import Waterproof.definitions.inequality_chains.
Require Import Waterproof.notations.notations.
Require Import Reals.
Require Import Reals.ROrderedType.
Require Import Coq.micromega.Lra.
Require Import Coq.micromega.Lia.
Require Import Waterproof.tactics.simplify_chains.
Require Import Waterproof.waterprove.simplify_subsets.

Require Import Waterproof.populate_database.waterproof_intuition.
Require Import Waterproof.populate_database.waterproof_firstorder.
Require Import Waterproof.populate_database.waterproof_negation_nat.
Require Import Waterproof.populate_database.waterproof_negation_int.
Require Import Waterproof.populate_database.waterproof_negation_reals.
Require Import Waterproof.populate_database.waterproof_decidability_reals.
Require Import Waterproof.populate_database.waterproof_decidability_nat.
Require Import Waterproof.populate_database.waterproof_eq_plus.
Require Import Waterproof.populate_database.waterproof_eq_zero.
Require Import Waterproof.populate_database.waterproof_eq_opp.
Require Import Waterproof.populate_database.waterproof_eq_one.
Require Import Waterproof.populate_database.waterproof_eq_mult.
Require Import Waterproof.populate_database.waterproof_eq_minus.
Require Import Waterproof.populate_database.waterproof_eq_abs.
Require Import Waterproof.populate_database.waterproof_eq_sqr.
Require Import Waterproof.populate_database.waterproof_eq_exp.

(* Hint to solve inequality chains. Redundant when using the waterprove subroutine. *)
Global Hint Extern 0 (total_statement _) => repeat split; cbn : core.
