(** * Populate Waterproof eq_opp database

Authors:
    - Jim Portegies
    - Jelle Wemmenhove

Creation date: 26 Mar 2023.

This file populates the Waterproof eq_opp database.

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

(** ** Populate the Waterproof eq_opp database *)

Require Import Reals.

Global Hint Extern 1 => (rewrite Ropp_minus_distr) :  eq_opp. 
  (* - (x - y) = y - x *)
Global Hint Extern 1 => (rewrite Ropp_minus_distr') :  eq_opp. 
  (* - (y - x) = x - y *)
Global Hint Extern 1 => (rewrite Ropp_mult_distr_l) :  eq_opp. 
  (* - (x * y) = - x * y *)
Global Hint Extern 1 => (rewrite Ropp_mult_distr_r) :  eq_opp.
  (* - (x * y) = x * - y *)
Global Hint Extern 1 => (rewrite Ropp_mult_distr_l_reverse) :  eq_opp. 
  (* - x * y = - (x * y) *)
Global Hint Extern 1 => (rewrite Ropp_mult_distr_r_reverse) :  eq_opp. 
  (* x * - y = - (x * y) *)
Global Hint Extern 1 => (rewrite Ropp_plus_distr) :  eq_opp. 
  (* - (x + y) = - x + - y. *)

(** #### Other 
We have some other properties:*)
Global Hint Extern 1 => (rewrite Ropp_involutive) :  eq_opp. (* --a = a *)
Global Hint Extern 1 => (rewrite Rmult_opp_opp) :  eq_opp. (* -a * -b = a * b *)
Global Hint Extern 1 => (rewrite Ropp_div) :  eq_opp. (* - a / b = - (a / b) *)
Global Hint Extern 1 => (rewrite Rplus_opp_l) :  eq_opp. (* -a  + a = 0 *)
Global Hint Extern 1 => (rewrite Rplus_opp_r) :  eq_opp. (* a  + -a = 0 *)
