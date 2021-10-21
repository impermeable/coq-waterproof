(** * [set_definitions.v]
Authors:
  - Jim Portegies
  - Jelle Wemmenhove
Creation date: 17 June 2021

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


(** * Definitions for sets*)
Require Import Reals.
Open Scope R_scope.
(** The following line automatically generates induction schemes for Records.*)
(*Set Nonrecursive Elimination Schemes. *)
Record     subset_R := mk_subset_R { pred_R :> R -> Prop }.
Record     elements_R (A : subset_R) := mk_elem_R { elem_R :> R; witness_R : A elem_R }.
Definition subset_to_elements_R := fun A : subset_R => elements_R A.
Coercion   subset_to_elements_R : subset_R >-> Sortclass.

