(** * Populate Waterproof decidability_reals database

Authors:
    - Jim Portegies
    - Jelle Wemmenhove

Creation date: 26 Mar 2023.

This file populates the Waterproof decidability_reals database.

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

(** ** Populate the Waterproof decidability_reals database *)

Require Import Reals.
Require Import Waterproof.theory.analysis.reals.

(** Automatically unfold > to <so (_ > _) no longer has to occur in the options below.
    We cannot do the same for >= as it is not defined as <= .*)
Global Hint Extern 1 => unfold Rgt : decidability_reals.

Global Hint Resolve Req_EM_T : decidability_reals.
Global Hint Resolve Rlt_le_dec : decidability_reals.
Global Hint Resolve Rlt_ge_dec : decidability_reals.

(** Lemmas to write e.g. `{r1 ≤ r2} + {~r2 ≥ r1}`.*)
Global Hint Resolve Rlt_dec Rle_dec Rge_dec : decidability_reals.
Global Hint Resolve Rle_ge_dec Rge_le_dec : decidability_reals.
Global Hint Resolve Rle_lt_or_eq_dec Rge_lt_or_eq_dec : decidability_reals.

Global Hint Resolve total_order_T : decidability_reals. (* x < y, x = y or y < x*)

