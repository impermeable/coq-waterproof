(** * Populate Waterproof eq_plus database

Authors:
    - Jim Portegies
    - Jelle Wemmenhove

Creation date: 26 Mar 2023.

This file populates the Waterproof eq_plus database.

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

(** ** Populate the Waterproof eq_plus database *)

Require Import Reals.

#[export] Hint Extern 1 => (rewrite Rplus_comm) :  eq_plus. (* x + y = y + x *)
#[export] Hint Extern 1 => (rewrite Rplus_assoc) :  eq_plus. (* x + y + z = x + (y + z) *)
#[export] Hint Extern 1 => (rewrite Rdiv_plus_distr) :  eq_plus. (* (x + y) / z = x / z + y / z *)
#[export] Hint Extern 1 => (rewrite Rmult_plus_distr_l) : eq_plus.
#[export] Hint Extern 1 => (rewrite Rmult_plus_distr_r) : eq_plus.
