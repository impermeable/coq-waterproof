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

Global Hint Resolve Rnot_le_lt : negation_reals.
Global Hint Resolve Rnot_ge_gt : negation_reals.
Global Hint Resolve Rnot_le_gt : negation_reals.
Global Hint Resolve Rnot_ge_lt : negation_reals.
Global Hint Resolve Rnot_lt_le : negation_reals.
Global Hint Resolve Rnot_gt_le : negation_reals.
Global Hint Resolve Rnot_gt_ge : negation_reals.
Global Hint Resolve Rnot_lt_ge : negation_reals.

Global Hint Resolve Rlt_not_le : negation_reals.
Global Hint Resolve Rgt_not_le : negation_reals.
Global Hint Resolve Rlt_not_ge : negation_reals.
Global Hint Resolve Rle_not_lt : negation_reals.
Global Hint Resolve Rge_not_lt : negation_reals.
Global Hint Resolve Rle_not_gt : negation_reals.
Global Hint Resolve Rge_not_gt : negation_reals.
