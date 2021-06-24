(** * set_definitions.v
Authors:
  - Jim Portegies
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
Set Nonrecursive Elimination Schemes.
Record elements_R_satisfying (pred : R -> Prop)
  := mk_element_R {
  element :> R;
  witness : pred element;
}.
Record subsets_R :=
  mk_subset_R {
  is_in : R -> Prop;
  elements := elements_R_satisfying is_in;
}.
Coercion subsets_R_to_elements :=
  (fun A : subsets_R => elements A).



