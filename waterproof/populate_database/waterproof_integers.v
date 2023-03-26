(** * Populate the waterproof_integers database

Authors:
    - Jim Portegies
    - Jelle Wemmenhove

Creation date: 26 Mar 2023.

This file populates the waterproof_integers database.

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

(** * Populate the waterproof_integers database. *)

(** TODO: importing Reals seems overkill, it should be enough to be able to import the ring tactic. *)
Require Import Reals.
Require Import Coq.micromega.Lia.
Require Import Waterproof.tactics.simplify_chains.

#[export] Hint Extern 3 ( _ = _ ) => cbn; ltac2:(simpl_ineq_chains ()); ring : waterproof_integers.
#[export] Hint Extern 3 ( @eq nat _  _) => cbn; ltac2:(simpl_ineq_chains ()); lia : waterproof_integers.
#[export] Hint Extern 3 ( le _ _ ) => cbn; ltac2:(simpl_ineq_chains ()); lia : waterproof_integers.
#[export] Hint Extern 3 ( ge _ _ ) => cbn; ltac2:(simpl_ineq_chains ()); lia : waterproof_integers.
#[export] Hint Extern 3 ( lt _ _ ) => cbn; ltac2:(simpl_ineq_chains ()); lia : waterproof_integers.
#[export] Hint Extern 3 ( gt _ _ ) => cbn; ltac2:(simpl_ineq_chains ()); lia : waterproof_integers.