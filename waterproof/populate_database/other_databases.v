(** * [databases.v]

Authors: 
    - Adrian Vramulet (1284487)
    - Tudor Voicu (1339532)
    - Lulof Pirée (1363638)
    - Cosmin Manea (1298542)
Creation date: 14 June 2021

In this file, we construct so-called Hint Databases.
These databases can be used in combination with the tactics 
`auto` and `eauto`.
When using such a tactic, 
the hints in the database are recursively called 
until a certain search depth (standard is 5).
We choose to split the interesting hints among a number 
of different databases, so that the recursive search
size and the corresponding search time remain relatively small.

--------------------------------------------------------------------------------

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


Require Import Coq.Logic.PropExtensionality.
Require Import Waterproof.definitions.set_definitions.
Require Import Waterproof.definitions.inequality_chains.
Require Import Waterproof.notations.notations.
Require Import Reals.
Require Import Reals.ROrderedType.
Require Import Coq.micromega.Lra.
Require Import Coq.micromega.Lia.
Require Import Waterproof.tactics.simplify_chains.
Require Import Waterproof.waterprove.simplify_subsets.

(** ** Additional database *)

(* This is currently just a placeholder *)

Global Hint Resolve Rmax_l : additional.

(** ** Intuition database *)

Global Hint Extern 3 => intuition (auto 2 with core) : intuition.

(** ** Firstorder database *)

Global Hint Extern 3 => firstorder (auto 2 with core) : firstorder.


Open Scope R_scope.

(* subsets *)
Global Hint Extern 3 => ltac2:(simpl_member_subset ()); lra : reals. (*TODO: do we need a hint database for (reals-and-subsets)?*)
(* Global Hint Extern 3 => ltac2:(simpl_member_subset ()); lia : waterproof_integers. (* not yet needed? *) *)
Global Hint Extern 3 (pred R _ _) => simpl; lra : reals.

(* Hint to solve inequality chains. Redundant when using the waterprove subroutine. *)
Global Hint Extern 0 (total_statement _) => repeat split; cbn : core.





Require Import Reals.
Local Open Scope R_scope.
From Ltac2 Require Import Ltac2 Ident.
Require Import Ltac.
Require Import Ltac2.Init.

(** ### ** Plus, minus and multiplication rewriters**
In this database, we will add commutative, associative and distributative properties of numbers in combination with 
the $+$ operator. We let $x, y ∈ \mathbb{R}$.

#### Commutativity:
We have the following commutative properties:*)
Global Hint Extern 1 => (rewrite Rplus_comm) :  eq_plus. (* x + y = y + x *)
Global Hint Extern 1 => (rewrite Rmult_comm) :  eq_mult. (* x * y = y * x *)

(** #### Associativity
We have the following associative properties:*)
Global Hint Extern 1 => (rewrite Rplus_assoc) :  eq_plus. (* x + y + z = x + (y + z) *)
Global Hint Extern 1 => (rewrite Rmult_assoc) :  eq_mult. (* x * y * z = x * (y * z) *)

(** #### Distributivity
We have the following distributive properties:*)
Global Hint Extern 1 => (rewrite Rdiv_plus_distr) :  eq_plus. 
  (* (x + y) / z = x / z + y / z *)
Global Hint Extern 1 => (rewrite Rdiv_minus_distr) :  eq_minus. 
  (* (x - y) / z = x / z - y / z *)
Global Hint Extern 1 => (rewrite Rmult_plus_distr_l) :  eq_mult eq_plus. 
  (* x * (y+z) = x * y + x * z *)
Global Hint Extern 1 => (rewrite Rmult_plus_distr_r) :  eq_mult eq_plus. 
  (* (x+y) * z = x * z + y * z *)

(** #### Other
We have some other properties:
*)
Global Hint Extern 1 => (unfold Rminus) : eq_minus.
(** ### **Opposite rewriters**
In this database, we will add properties with the additive inverse.*)
(** #### Distributitivity
We have the following distributive properties containing additive inverses:*)
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

(** ### **Simple number arithmetic**
Addition with 0 and multiplication with 0 or 1 is a trivial task, so we use two databases to resolve such simple steps.

#### Arithmetic with 0's
We have the following properties for equations with 0:*)
Global Hint Extern 1 => (rewrite Rplus_0_l) :  eq_zero. (* 0 + x = x *)
Global Hint Extern 1 => (rewrite Rplus_0_r) :  eq_zero. (* x + 0 = x *)
Global Hint Extern 1 => (rewrite Rminus_0_l) :  eq_zero. (* 0 - x = - x *)
Global Hint Extern 1 => (rewrite Rminus_0_r) :  eq_zero. (* x - 0 = x *)
Global Hint Extern 1 => (rewrite Rmult_0_l) :  eq_zero. (* 0 * x = 0 *)
Global Hint Extern 1 => (rewrite Rmult_0_r) :  eq_zero. (* x * 0 = 0 *)
Global Hint Extern 1 => (rewrite pow_O) :  eq_zero. (* x ^ 0 = 1 *)
(** #### Arithmetic with 1's
We have the following properties for equations with 1:*)
Global Hint Extern 1 => (rewrite Rmult_1_l) :  eq_one. (* 1 * x = x *)
Global Hint Extern 1 => (rewrite Rmult_1_r) :  eq_one. (* x * 1 = x *)
Global Hint Extern 1 => (rewrite Rinv_1) :  eq_one. (* x / 1 = x *)
Global Hint Extern 1 => (rewrite pow_1) :  eq_one. (* x ^ 1 = x *)
Global Hint Extern 1 => (rewrite Rinv_inv) : eq_one. (* / / x = x *)






(** ### **Distances and absolute values**
There are a number of trivial steps regarding distances, or absolute values.

#### Distance (R_dist)
We have the following properties:*)
Global Hint Extern 1 => (rewrite R_dist_eq) :  eq_abs. 
  (* ||a - a|| = 0 *)
Global Hint Extern 1 => (rewrite R_dist_mult_l) :  eq_abs. 
  (* ||a * b - a * c|| = ||a|| * ||b - c|| *)
Global Hint Extern 1 => (rewrite R_dist_sym) :  eq_abs. 
  (*||a - b|| = ||b - a||*)
(** #### Absolute value (Rabs)
We have the following properties:*)
Global Hint Extern 1 => (rewrite Rabs_minus_sym) :  eq_abs. 
  (* |a - b| = |b - a|, using Rabs *)
Global Hint Extern 1 => (rewrite Rabs_Rabsolu) :  eq_abs. 
  (* | |a| | = |a| *)
Global Hint Extern 1 => (rewrite Rabs_Ropp) :  eq_abs. 
  (* |-a| = |a| *)
Global Hint Extern 1 => (rewrite Rabs_mult) :  eq_abs. 
  (* |a * b| = |a| * |b| *)
Global Hint Extern 1 => (rewrite Rsqr_abs) :  eq_abs. 
  (* a^2 = |a|^2 *)
Global Hint Extern 1 => (rewrite sqrt_Rsqr_abs) :  eq_abs. 
  (* sqrt(a^2) = |a| *)
Global Hint Extern 1 => (rewrite pow2_abs) :  eq_abs. 
  (* | a |^2 = a^2*)





(** ### **Squares**
There are a number of trivial steps regarding squares.
We have the following properties:*)
Global Hint Extern 1 => (rewrite Rsqr_pow2) :  eq_sqr. (* a² = a ^ 2 *)
Global Hint Extern 1 => (rewrite Rsqr_plus) :  eq_sqr. (* (a-b)² = a² + b² + 2*a*b *)
Global Hint Extern 1 => (rewrite Rsqr_plus_minus) :  eq_sqr. (* (a+b)*(a-b) = a² - b² *)
Global Hint Extern 1 => (rewrite Rsqr_minus) :  eq_sqr. (* (a-b)² = a² + b² - 2*a*b *)
Global Hint Extern 1 => (rewrite Rsqr_minus_plus) :  eq_sqr. (* (a-b)*(a+b) = a² - b² *)
Global Hint Extern 1 => (rewrite Rsqr_neg) :  eq_sqr. (* a² = (-a)² *)
Global Hint Extern 1 => (rewrite Rsqr_neg_minus) :  eq_sqr. (* (a-b)² = (b-a)² *)
Global Hint Extern 1 => (rewrite Rsqr_mult) :  eq_sqr. (* (a*b)² = a² * b² *)





(** ### **Exponentials**
There are a number of trivial steps regarding exponentials. We have the following properties:*)
Global Hint Extern 1 => (rewrite ln_exp) :  eq_exp. (* ln (exp a)) = a *)
Global Hint Extern 1 => (rewrite exp_Ropp) :  eq_exp. (* exp (-a) = / exp a*)
Global Hint Extern 1 => (rewrite exp_plus) :  eq_exp. (* exp(a+b) = exp(a) * exp(b) *)
Global Hint Extern 1 => (rewrite ln_exp) :  eq_exp. (* ln (exp a)) = a *)


Close Scope R_scope.


(** ## Lemmas for dealing with negations in specific contexts, e.g. negated order relations
*)
(** * Naturals *)
Global Hint Resolve Nat.le_ngt : negation_nat.
Global Hint Resolve not_lt : negation_nat.
Global Hint Resolve not_le : negation_nat.

(** * Integers *) (* TODO add more to make automation faster*)
Global Hint Resolve  Zle_not_lt : negation_int.
Global Hint Resolve  Zlt_not_le : negation_int.
Global Hint Resolve  Zle_not_gt : negation_int.
Global Hint Resolve  Zgt_not_le : negation_int.
Global Hint Resolve  Znot_lt_ge : negation_int.
Global Hint Resolve  Znot_lt_ge : negation_int.
Global Hint Resolve  Znot_gt_le : negation_int.
Global Hint Resolve  Znot_le_gt : negation_int.

(** * Reals *) (* TODO add more to make automation faster*)

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





(** ## Lemmas for decidability. *)
(** * Reals *)
Local Open Scope R_scope.

(** Automatically unfold > to <so (_ > _) no longer has to occur in the options below.
    We cannot do the same for >= as it is not defined as <= .*)
Global Hint Extern 1 => unfold Rgt : decidability_reals.

Global Hint Resolve Req_EM_T : decidability_reals.

(* Natural numbers *)
Global Hint Resolve Nat.eq_dec : decidability_nat. (* TODO: add more! *)

Close Scope R_scope.
