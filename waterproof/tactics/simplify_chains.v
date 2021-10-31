(** * [simplify_chains.v]
Authors: 
    - Jim Portegies
Creation date: 31 Oct 2021

Tactic to simplify (in)equalitiy chains.

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
From Ltac2 Require Option.
From Ltac2 Require Import Message.

Require Import Waterproof.auxiliary.
Require Import Waterproof.definitions.inequality_chains.
Require Import Waterproof.tactics.goal_wrappers.

(**  ** simpl_ineq_chains

Writes out an inequality chain as a big conjunction.

*)
Ltac2 simpl_ineq_chains () :=
    repeat (
        match! goal with
(** TODO: do this in a more structured way *)
        | [ h : inequality_chains_R.ineq_to_prop _ |- _ ] => 
            unfold inequality_chains_R.ineq_to_prop in $h;
            unfold inequality_chains_R.ineq_to_prop in $h;
            unfold inequality_chains_R.prop_list_and in $h;
            simpl in $h
        | [ h : inequality_chains_nat.ineq_to_prop _ |- _ ] => 
            unfold inequality_chains_nat.ineq_to_prop in $h;
            unfold inequality_chains_nat.ineq_to_prop in $h;
            unfold inequality_chains_nat.prop_list_and in $h;
            simpl in $h
        | [ |- _ ] => ()
        end
    ).