(** * [simplify_subsets.v]
Authors: 
    - Jelle Wemmenhove
Creation date: 29 April 2022

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
Require Import Waterproof.definitions.set_definitions.
(**  ** simpl_member_subset

Writes out membership of a subset [x : A] as satisfying [A]'s defining predicate [P x],
where $A := {x : X | (P x) holds}$.

*)

Ltac2 simpl_member_subset () :=
    repeat (
        match! goal with
        | [ h : (pred _ _) _ |- _ ] => simpl in $h
        | [ |- _ ] => ()
        end
    ).