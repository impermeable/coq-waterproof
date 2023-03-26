(** * Populate the waterproof_core database

Authors:
    - Jim Portegies
    - Jelle Wemmenhove

Creation date: 26 Mar 2023.

This file populates the waterproof_core database.

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

(** * Populate the waterproof_core database. *)

Require Import Waterproof.definitions.inequality_chains.
Require Import Waterproof.tactics.simplify_chains.

(* Hint to solve inequality chains. Redundant when using the waterprove subroutine. *)
Global Hint Extern 0 (total_statement _) => repeat split; cbn : waterproof_core.

Global Hint Extern 1 ( _ = _ ) => cbn; ltac2:(simpl_ineq_chains ()); ltac2:(split_conjunctions ()) : waterproof_core.
Global Hint Resolve f_equal : waterproof_core.
Global Hint Resolve f_equal2 : waterproof_core.
Global Hint Extern 1 ( _ = _ ) => congruence : waterproof_core.
