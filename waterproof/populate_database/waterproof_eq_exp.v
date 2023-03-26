(** * Populate Waterproof eq_exp database

Authors:
    - Jim Portegies
    - Jelle Wemmenhove

Creation date: 26 Mar 2023.

This file populates the Waterproof eq_exp database.

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

(** ** Populate the Waterproof eq_exp database *)

Require Import Reals.

Global Hint Extern 1 => (rewrite ln_exp) :  eq_exp. (* ln (exp a)) = a *)
Global Hint Extern 1 => (rewrite exp_Ropp) :  eq_exp. (* exp (-a) = / exp a*)
Global Hint Extern 1 => (rewrite exp_plus) :  eq_exp. (* exp(a+b) = exp(a) * exp(b) *)
Global Hint Extern 1 => (rewrite ln_exp) :  eq_exp. (* ln (exp a)) = a *)
