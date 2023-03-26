(** * Populate Waterproof eq_abs database

Authors:
    - Jim Portegies
    - Jelle Wemmenhove

Creation date: 26 Mar 2023.

This file populates the Waterproof eq_abs database.

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

(** ** Populate the Waterproof eq_abs database *)

Require Import Reals.

#[export] Hint Extern 1 => (rewrite R_dist_eq) :  eq_abs. 
  (* ||a - a|| = 0 *)
#[export] Hint Extern 1 => (rewrite R_dist_mult_l) :  eq_abs. 
  (* ||a * b - a * c|| = ||a|| * ||b - c|| *)
#[export] Hint Extern 1 => (rewrite R_dist_sym) :  eq_abs. 
  (*||a - b|| = ||b - a||*)
(** #### Absolute value (Rabs)
We have the following properties:*)
#[export] Hint Extern 1 => (rewrite Rabs_minus_sym) :  eq_abs. 
  (* |a - b| = |b - a|, using Rabs *)
#[export] Hint Extern 1 => (rewrite Rabs_Rabsolu) :  eq_abs. 
  (* | |a| | = |a| *)
#[export] Hint Extern 1 => (rewrite Rabs_Ropp) :  eq_abs. 
  (* |-a| = |a| *)
#[export] Hint Extern 1 => (rewrite Rabs_mult) :  eq_abs. 
  (* |a * b| = |a| * |b| *)
#[export] Hint Extern 1 => (rewrite Rsqr_abs) :  eq_abs. 
  (* a^2 = |a|^2 *)
#[export] Hint Extern 1 => (rewrite sqrt_Rsqr_abs) :  eq_abs. 
  (* sqrt(a^2) = |a| *)
#[export] Hint Extern 1 => (rewrite pow2_abs) :  eq_abs. 
  (* | a |^2 = a^2*)
