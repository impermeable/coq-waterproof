(** * Populate Waterproof eq_one database

Authors:
    - Jim Portegies
    - Jelle Wemmenhove

Creation date: 26 Mar 2023.

This file populates the Waterproof eq_one database.

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

(** ** Populate the Waterproof eq_one database *)

Require Import Reals.

Global Hint Extern 1 => (rewrite Rmult_1_l) :  eq_one. (* 1 * x = x *)
Global Hint Extern 1 => (rewrite Rmult_1_r) :  eq_one. (* x * 1 = x *)
Global Hint Extern 1 => (rewrite Rinv_1) :  eq_one. (* x / 1 = x *)
Global Hint Extern 1 => (rewrite pow_1) :  eq_one. (* x ^ 1 = x *)
Global Hint Extern 1 => (rewrite Rinv_inv) : eq_one. (* / / x = x *)
