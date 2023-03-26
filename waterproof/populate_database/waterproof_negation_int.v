(** * Populate Waterproof negation_reals database

Authors:
    - Jim Portegies
    - Jelle Wemmenhove

Creation date: 26 Mar 2023.

This file populates the Waterproof negation_reals database.

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

(** ** Populate the Waterproof negation_reals database *)

Require Import Reals.

(** * Integers *) (* TODO add more to make automation faster*)
#[export] Hint Resolve  Zle_not_lt : negation_int.
#[export] Hint Resolve  Zlt_not_le : negation_int.
#[export] Hint Resolve  Zle_not_gt : negation_int.
#[export] Hint Resolve  Zgt_not_le : negation_int.
#[export] Hint Resolve  Znot_lt_ge : negation_int.
#[export] Hint Resolve  Znot_lt_ge : negation_int.
#[export] Hint Resolve  Znot_gt_le : negation_int.
#[export] Hint Resolve  Znot_le_gt : negation_int.