(** * Populate Waterproof eq_sqr database

Authors:
    - Jim Portegies
    - Jelle Wemmenhove

Creation date: 26 Mar 2023.

This file populates the Waterproof eq_sqr database.

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

(** ** Populate the Waterproof eq_sqr database *)

Require Import Reals.

Global Hint Extern 1 => (rewrite Rsqr_pow2) :  eq_sqr. (* a² = a ^ 2 *)
Global Hint Extern 1 => (rewrite Rsqr_plus) :  eq_sqr. (* (a-b)² = a² + b² + 2*a*b *)
Global Hint Extern 1 => (rewrite Rsqr_plus_minus) :  eq_sqr. (* (a+b)*(a-b) = a² - b² *)
Global Hint Extern 1 => (rewrite Rsqr_minus) :  eq_sqr. (* (a-b)² = a² + b² - 2*a*b *)
Global Hint Extern 1 => (rewrite Rsqr_minus_plus) :  eq_sqr. (* (a-b)*(a+b) = a² - b² *)
Global Hint Extern 1 => (rewrite Rsqr_neg) :  eq_sqr. (* a² = (-a)² *)
Global Hint Extern 1 => (rewrite Rsqr_neg_minus) :  eq_sqr. (* (a-b)² = (b-a)² *)
Global Hint Extern 1 => (rewrite Rsqr_mult) :  eq_sqr. (* (a*b)² = a² * b² *)
