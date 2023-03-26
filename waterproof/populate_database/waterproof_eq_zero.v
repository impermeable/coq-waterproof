(** * Populate Waterproof eq_zero database

Authors:
    - Jim Portegies
    - Jelle Wemmenhove

Creation date: 26 Mar 2023.

This file populates the Waterproof eq_zero database.

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

(** ** Populate the Waterproof eq_zero database *)

Require Import Reals.

(** We have the following properties for equations with 0:*)
#[export] Hint Extern 1 => (rewrite Rplus_0_l) :  eq_zero. (* 0 + x = x *)
#[export] Hint Extern 1 => (rewrite Rplus_0_r) :  eq_zero. (* x + 0 = x *)
#[export] Hint Extern 1 => (rewrite Rminus_0_l) :  eq_zero. (* 0 - x = - x *)
#[export] Hint Extern 1 => (rewrite Rminus_0_r) :  eq_zero. (* x - 0 = x *)
#[export] Hint Extern 1 => (rewrite Rmult_0_l) :  eq_zero. (* 0 * x = 0 *)
#[export] Hint Extern 1 => (rewrite Rmult_0_r) :  eq_zero. (* x * 0 = 0 *)
#[export] Hint Extern 1 => (rewrite pow_O) :  eq_zero. (* x ^ 0 = 1 *)
