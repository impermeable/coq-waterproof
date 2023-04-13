(** * Module for loading databases
Authors: 
    - Jim Portegies
Creation date: 29 Mar 2023

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

Module Type preloader.
End preloader.

Require Waterproof.waterprove.manipulate_negation.
Require Classical_Pred_Type.
Require Waterproof.definitions.inequality_chains.
Require Waterproof.tactics.simplify_chains.
Require Reals.
Require Coq.micromega.Lia.
Require Sets.Ensembles.
Require Sets.Classical_sets.
Require Waterproof.waterprove.simplify_subsets.
Require Coq.Logic.ClassicalEpsilon.
Require Waterproof.theory.logic_and_set_theory.classical_logic.
Require Waterproof.theory.logic_and_set_theory.subsets.
Require Waterproof.theory.analysis.reals.
Require Waterproof.theory.logic_and_set_theory.subsets.
Require Waterproof.tactics.sets_tactics.sets_automation_tactics.

Module wp_classical_logic <: preloader.

Import manipulate_negation.
Import Classical_Pred_Type.
Import Waterproof.theory.logic_and_set_theory.classical_logic.

#[export] Hint Resolve not_ex_all_not : wp_classical_logic.
#[export] Hint Resolve ex_not_not_all : wp_classical_logic.
#[export] Hint Resolve all_not_not_ex : wp_classical_logic.
#[export] Hint Resolve not_all_not_ex : wp_classical_logic.
#[export] Hint Resolve not_all_ex_not : wp_classical_logic.
#[export] Hint Extern 1 => ltac2:(solve_by_manipulating_negation ()) : wp_classical_logic.

(* not_ex_not_all cannot be used as a hint. *)
(* #[export] Hint Resolve not_ex_not_all : classical_logic. *)

End wp_classical_logic.

Module wp_constructive_logic <: preloader.

(** TODO: fix this import. *)
Import Classical_Pred_Type.

#[export] Hint Resolve not_ex_all_not : wp_constructive_logic.
#[export] Hint Resolve ex_not_not_all : wp_constructive_logic.
#[export] Hint Resolve all_not_not_ex : wp_constructive_logic.

End wp_constructive_logic.

Module wp_core <: preloader.

Import Waterproof.definitions.inequality_chains.
Import Waterproof.tactics.simplify_chains.

(* Hint to solve inequality chains. Redundant when using the waterprove subroutine. *)
#[export] Hint Extern 0 (total_statement _) => repeat split; cbn : wp_core.

#[export] Hint Extern 1 ( _ = _ ) => cbn; ltac2:(simpl_ineq_chains ()); ltac2:(split_conjunctions ()) : wp_core.
#[export] Hint Resolve eq_sym : wp_core.
#[export] Hint Resolve f_equal : wp_core.
#[export] Hint Resolve f_equal2 : wp_core.
#[export] Hint Extern 1 ( _ = _ ) => congruence : wp_core.

End wp_core.

Module wp_decidability_classical <: preloader.

(** ** We take informative excluded middle from Classical Epsilon *)
Import Coq.Logic.ClassicalEpsilon.

#[export] Hint Resolve excluded_middle_informative : wp_decidability_classical.

End wp_decidability_classical.

Module wp_decidability_nat <: preloader.

(** TODO: make this import less broad *)
Import Reals.

(* Natural numbers *)
#[export] Hint Resolve Nat.eq_dec : wp_decidability_nat. (* TODO: add more! *)

End wp_decidability_nat.

Module wp_decidability_reals <: preloader.

Import Reals.
Import Waterproof.theory.analysis.reals.

(** Automatically unfold > to <so (_ > _) no longer has to occur in the options below.
    We cannot do the same for >= as it is not defined as <= .*)
#[export] Hint Extern 1 => unfold Rgt : wp_decidability_reals.

#[export] Hint Resolve Req_EM_T : wp_decidability_reals.
#[export] Hint Resolve Rlt_le_dec : wp_decidability_reals.
#[export] Hint Resolve Rlt_ge_dec : wp_decidability_reals.

(** Lemmas to write e.g. `{r1 ≤ r2} + {~r2 ≥ r1}`.*)
#[export] Hint Resolve Rlt_dec Rle_dec Rge_dec : wp_decidability_reals.
#[export] Hint Resolve Rle_ge_dec Rge_le_dec : wp_decidability_reals.
#[export] Hint Resolve Rle_lt_or_eq_dec Rge_lt_or_eq_dec : wp_decidability_reals.

#[export] Hint Resolve total_order_T : wp_decidability_reals. (* x < y, x = y or y < x*)

End wp_decidability_reals.

Module wp_eq_abs <: preloader.

Import Reals.

#[export] Hint Extern 1 => (rewrite R_dist_eq) : wp_eq_abs. 
  (* ||a - a|| = 0 *)
#[export] Hint Extern 1 => (rewrite R_dist_mult_l) : wp_eq_abs. 
  (* ||a * b - a * c|| = ||a|| * ||b - c|| *)
#[export] Hint Extern 1 => (rewrite R_dist_sym) : wp_eq_abs. 
  (*||a - b|| = ||b - a||*)
(** #### Absolute value (Rabs)
We have the following properties:*)
#[export] Hint Extern 1 => (rewrite Rabs_minus_sym) : wp_eq_abs. 
  (* |a - b| = |b - a|, using Rabs *)
#[export] Hint Extern 1 => (rewrite Rabs_Rabsolu) : wp_eq_abs. 
  (* | |a| | = |a| *)
#[export] Hint Extern 1 => (rewrite Rabs_Ropp) : wp_eq_abs. 
  (* |-a| = |a| *)
#[export] Hint Extern 1 => (rewrite Rabs_mult) : wp_eq_abs. 
  (* |a * b| = |a| * |b| *)
#[export] Hint Extern 1 => (rewrite Rsqr_abs) : wp_eq_abs. 
  (* a^2 = |a|^2 *)
#[export] Hint Extern 1 => (rewrite sqrt_Rsqr_abs) : wp_eq_abs. 
  (* sqrt(a^2) = |a| *)
#[export] Hint Extern 1 => (rewrite pow2_abs) : wp_eq_abs. 
  (* | a |^2 = a^2*)

End wp_eq_abs.

Module wp_eq_exp.

Import Reals.

#[export] Hint Extern 1 => (rewrite ln_exp) : wp_eq_exp. (* ln (exp a)) = a *)
#[export] Hint Extern 1 => (rewrite exp_Ropp) : wp_eq_exp. (* exp (-a) = / exp a*)
#[export] Hint Extern 1 => (rewrite exp_plus) : wp_eq_exp. (* exp(a+b) = exp(a) * exp(b) *)
#[export] Hint Extern 1 => (rewrite ln_exp) : wp_eq_exp. (* ln (exp a)) = a *)

End wp_eq_exp.

Module wp_eq_minus <: preloader.

Import Reals.

#[export] Hint Extern 1 => (rewrite Rdiv_minus_distr) :  wp_eq_minus. 
  (* (x - y) / z = x / z - y / z *)
#[export] Hint Extern 1 => (unfold Rminus) : wp_eq_minus.

End wp_eq_minus.

Module wp_eq_mult <: preloader.

Import Reals.

#[export] Hint Extern 1 => (rewrite Rmult_comm) : wp_eq_mult. (* x * y = y * x *)

(** #### Associativity
We have the following associative properties:*)

#[export] Hint Extern 1 => (rewrite Rmult_assoc) : wp_eq_mult. (* x * y * z = x * (y * z) *)
#[export] Hint Extern 1 => (rewrite Rmult_plus_distr_l) : wp_eq_mult eq_plus. 
  (* x * (y+z) = x * y + x * z *)
#[export] Hint Extern 1 => (rewrite Rmult_plus_distr_r) : wp_eq_mult eq_plus. 
  (* (x+y) * z = x * z + y * z *)

End wp_eq_mult.

Module wp_eq_one <: preloader.

Import Reals.

#[export] Hint Extern 1 => (rewrite Rmult_1_l) : wp_eq_one. (* 1 * x = x *)
#[export] Hint Extern 1 => (rewrite Rmult_1_r) : wp_eq_one. (* x * 1 = x *)
#[export] Hint Extern 1 => (rewrite Rinv_1) : wp_eq_one. (* x / 1 = x *)
#[export] Hint Extern 1 => (rewrite pow_1) : wp_eq_one. (* x ^ 1 = x *)
#[export] Hint Extern 1 => (rewrite Rinv_inv) : wp_eq_one. (* / / x = x *)

End wp_eq_one.

Module wp_eq_opp <: preloader.

Import Reals.

#[export] Hint Extern 1 => (rewrite Ropp_minus_distr) : wp_eq_opp.
  (* - (x - y) = y - x *)
#[export] Hint Extern 1 => (rewrite Ropp_minus_distr') : wp_eq_opp.
  (* - (y - x) = x - y *)
#[export] Hint Extern 1 => (rewrite Ropp_mult_distr_l) : wp_eq_opp.
  (* - (x * y) = - x * y *)
#[export] Hint Extern 1 => (rewrite Ropp_mult_distr_r) : wp_eq_opp.
  (* - (x * y) = x * - y *)
#[export] Hint Extern 1 => (rewrite Ropp_mult_distr_l_reverse) : wp_eq_opp.
  (* - x * y = - (x * y) *)
#[export] Hint Extern 1 => (rewrite Ropp_mult_distr_r_reverse) : wp_eq_opp.
  (* x * - y = - (x * y) *)
#[export] Hint Extern 1 => (rewrite Ropp_plus_distr) : wp_eq_opp.
  (* - (x + y) = - x + - y. *)

(** #### Other 
We have some other properties:*)
#[export] Hint Extern 1 => (rewrite Ropp_involutive) : wp_eq_opp. (* --a = a *)
#[export] Hint Extern 1 => (rewrite Rmult_opp_opp) : wp_eq_opp. (* -a * -b = a * b *)
#[export] Hint Extern 1 => (rewrite Ropp_div) : wp_eq_opp. (* - a / b = - (a / b) *)
#[export] Hint Extern 1 => (rewrite Rplus_opp_l) : wp_eq_opp. (* -a  + a = 0 *)
#[export] Hint Extern 1 => (rewrite Rplus_opp_r) : wp_eq_opp. (* a  + -a = 0 *)

End wp_eq_opp.

Module wp_eq_plus <: preloader.

Import Reals.

#[export] Hint Extern 1 => (rewrite Rplus_comm) : wp_eq_plus. (* x + y = y + x *)
#[export] Hint Extern 1 => (rewrite Rplus_assoc) : wp_eq_plus. (* x + y + z = x + (y + z) *)
#[export] Hint Extern 1 => (rewrite Rdiv_plus_distr) : wp_eq_plus. (* (x + y) / z = x / z + y / z *)
#[export] Hint Extern 1 => (rewrite Rmult_plus_distr_l) : wp_eq_plus.
#[export] Hint Extern 1 => (rewrite Rmult_plus_distr_r) : wp_eq_plus.

End wp_eq_plus.

Module wp_eq_sqr <: preloader.

Import Reals.

#[export] Hint Extern 1 => (rewrite Rsqr_pow2) : wp_eq_sqr. (* a² = a ^ 2 *)
#[export] Hint Extern 1 => (rewrite Rsqr_plus) : wp_eq_sqr. (* (a-b)² = a² + b² + 2*a*b *)
#[export] Hint Extern 1 => (rewrite Rsqr_plus_minus) : wp_eq_sqr. (* (a+b)*(a-b) = a² - b² *)
#[export] Hint Extern 1 => (rewrite Rsqr_minus) : wp_eq_sqr. (* (a-b)² = a² + b² - 2*a*b *)
#[export] Hint Extern 1 => (rewrite Rsqr_minus_plus) : wp_eq_sqr. (* (a-b)*(a+b) = a² - b² *)
#[export] Hint Extern 1 => (rewrite Rsqr_neg) : wp_eq_sqr. (* a² = (-a)² *)
#[export] Hint Extern 1 => (rewrite Rsqr_neg_minus) : wp_eq_sqr. (* (a-b)² = (b-a)² *)
#[export] Hint Extern 1 => (rewrite Rsqr_mult) : wp_eq_sqr. (* (a*b)² = a² * b² *)

End wp_eq_sqr.

Module wp_eq_zero <: preloader.

Import Reals.

(** We have the following properties for equations with 0:*)
#[export] Hint Extern 1 => (rewrite Rplus_0_l) : wp_eq_zero. (* 0 + x = x *)
#[export] Hint Extern 1 => (rewrite Rplus_0_r) : wp_eq_zero. (* x + 0 = x *)
#[export] Hint Extern 1 => (rewrite Rminus_0_l) : wp_eq_zero. (* 0 - x = - x *)
#[export] Hint Extern 1 => (rewrite Rminus_0_r) : wp_eq_zero. (* x - 0 = x *)
#[export] Hint Extern 1 => (rewrite Rmult_0_l) : wp_eq_zero. (* 0 * x = 0 *)
#[export] Hint Extern 1 => (rewrite Rmult_0_r) : wp_eq_zero. (* x * 0 = 0 *)
#[export] Hint Extern 1 => (rewrite pow_O) : wp_eq_zero. (* x ^ 0 = 1 *)

End wp_eq_zero.

Module wp_firstorder <: preloader.

#[export] Hint Extern 3 => firstorder (auto 2 with core) : wp_firstorder.

End wp_firstorder.

Module wp_integers <: preloader.

(** TODO: importing Reals seems overkill, it should be enough to be able to import the ring tactic. *)
Import Reals.
Import Coq.micromega.Lia.
Import Waterproof.tactics.simplify_chains.

#[export] Hint Extern 3 ( _ = _ ) => cbn; ltac2:(simpl_ineq_chains ()); ring : wp_integers.
#[export] Hint Extern 3 ( @eq nat _  _) => cbn; ltac2:(simpl_ineq_chains ()); lia : wp_integers.
#[export] Hint Extern 3 ( le _ _ ) => cbn; ltac2:(simpl_ineq_chains ()); lia : wp_integers.
#[export] Hint Extern 3 ( ge _ _ ) => cbn; ltac2:(simpl_ineq_chains ()); lia : wp_integers.
#[export] Hint Extern 3 ( lt _ _ ) => cbn; ltac2:(simpl_ineq_chains ()); lia : wp_integers.
#[export] Hint Extern 3 ( gt _ _ ) => cbn; ltac2:(simpl_ineq_chains ()); lia : wp_integers.

End wp_integers.

Module wp_intuition <: preloader.

#[export] Hint Extern 3 => intuition (auto 2 with core) : wp_intuition.

End wp_intuition.

Module wp_negation_int <: preloader.

Import Reals.

(** * Integers *) (* TODO add more to make automation faster*)
#[export] Hint Resolve  Zle_not_lt : wp_negation_int.
#[export] Hint Resolve  Zlt_not_le : wp_negation_int.
#[export] Hint Resolve  Zle_not_gt : wp_negation_int.
#[export] Hint Resolve  Zgt_not_le : wp_negation_int.
#[export] Hint Resolve  Znot_lt_ge : wp_negation_int.
#[export] Hint Resolve  Znot_lt_ge : wp_negation_int.
#[export] Hint Resolve  Znot_gt_le : wp_negation_int.
#[export] Hint Resolve  Znot_le_gt : wp_negation_int.

End wp_negation_int.

Module wp_negation_nat <: preloader.

(** TODO: change the import to something less big *)
Import Reals.

(** * Naturals *)
#[export] Hint Resolve Nat.le_ngt : wp_negation_nat.
#[export] Hint Resolve not_lt : wp_negation_nat.
#[export] Hint Resolve not_le : wp_negation_nat.

End wp_negation_nat.

Module wp_negation_reals <: preloader.

Import Reals.

#[export] Hint Resolve Rnot_le_lt : wp_negation_reals.
#[export] Hint Resolve Rnot_ge_gt : wp_negation_reals.
#[export] Hint Resolve Rnot_le_gt : wp_negation_reals.
#[export] Hint Resolve Rnot_ge_lt : wp_negation_reals.
#[export] Hint Resolve Rnot_lt_le : wp_negation_reals.
#[export] Hint Resolve Rnot_gt_le : wp_negation_reals.
#[export] Hint Resolve Rnot_gt_ge : wp_negation_reals.
#[export] Hint Resolve Rnot_lt_ge : wp_negation_reals.

#[export] Hint Resolve Rlt_not_le : wp_negation_reals.
#[export] Hint Resolve Rgt_not_le : wp_negation_reals.
#[export] Hint Resolve Rlt_not_ge : wp_negation_reals.
#[export] Hint Resolve Rle_not_lt : wp_negation_reals.
#[export] Hint Resolve Rge_not_lt : wp_negation_reals.
#[export] Hint Resolve Rle_not_gt : wp_negation_reals.
#[export] Hint Resolve Rge_not_gt : wp_negation_reals.

End wp_negation_reals.

Module wp_reals <: preloader.

Import Reals.
Import Coq.micromega.Lra.
Import Waterproof.tactics.simplify_chains.
Import Waterproof.waterprove.simplify_subsets.
Import Waterproof.theory.analysis.reals.

#[export] Hint Extern 3 => ltac2:(simpl_member_subset ()); lra : wp_reals. (*TODO: do we need a hint database for (reals-and-subsets)?*)
#[export] Hint Extern 3 (pred R _ _) => simpl; lra : wp_reals.

#[export] Hint Extern 3 ( @eq R _ _ ) => ltac2:(simpl_ineq_chains ()); field : wp_reals.

#[export] Hint Extern 3 ( Rle _ _ ) => cbn; ltac2:(simpl_ineq_chains ()); lra : wp_reals.
#[export] Hint Extern 3 ( Rge _ _ ) => cbn; ltac2:(simpl_ineq_chains ()); lra : wp_reals.
#[export] Hint Extern 3 ( Rlt _ _ ) => cbn; ltac2:(simpl_ineq_chains ()); lra : wp_reals.
#[export] Hint Extern 3 ( Rgt _ _ ) => cbn; ltac2:(simpl_ineq_chains ()); lra : wp_reals.

#[export] Hint Extern 3 (~ (Rle _ _) ) => cbn; ltac2:(simpl_ineq_chains ()); lra : wp_reals.
#[export] Hint Extern 3 (~ (Rge _ _) ) => cbn; ltac2:(simpl_ineq_chains ()); lra : wp_reals.
#[export] Hint Extern 3 (~ (Rlt _ _) ) => cbn; ltac2:(simpl_ineq_chains ()); lra : wp_reals.
#[export] Hint Extern 3 (~ (Rgt _ _) ) => cbn; ltac2:(simpl_ineq_chains ()); lra : wp_reals.
#[export] Hint Extern 3 (~ (@eq R _ _ ) ) => cbn; ltac2:(simpl_ineq_chains ()); lra : wp_reals.

#[export] Hint Extern 3 ( Rle _ _ ) => cbn; nra : wp_reals.
#[export] Hint Extern 3 ( Rge _ _ ) => cbn; nra : wp_reals.
#[export] Hint Extern 3 ( Rlt _ _ ) => cbn; nra : wp_reals.
#[export] Hint Extern 3 ( Rgt _ _ ) => cbn; nra : wp_reals.

#[export] Hint Resolve eq_sym : wp_reals.
#[export] Hint Resolve false_Req : wp_reals.
#[export] Hint Resolve true_Req : wp_reals.

#[export] Hint Resolve Rmin_l : wp_reals.
#[export] Hint Resolve Rmin_r : wp_reals.
#[export] Hint Resolve Rmax_l : wp_reals.
#[export] Hint Resolve Rmax_r : wp_reals.
#[export] Hint Resolve Rle_max_compat_l : wp_reals.
#[export] Hint Resolve Rle_max_compat_r : wp_reals.
#[export] Hint Resolve Rmax_lub : wp_reals.
#[export] Hint Resolve Rmax_lub_lt : wp_reals.
#[export] Hint Resolve Rmax_left : wp_reals.
#[export] Hint Resolve Rmax_right : wp_reals.
#[export] Hint Resolve Rmin_left : wp_reals.
#[export] Hint Resolve Rmin_right : wp_reals.
#[export] Hint Resolve Rmin_glb : wp_reals.
#[export] Hint Resolve Rmin_glb_lt : wp_reals.

#[export] Hint Resolve div_sign_flip : wp_reals.
#[export] Hint Resolve div_pos : wp_reals.
#[export] Hint Resolve inv_remove : wp_reals.
#[export] Hint Resolve Rinv_inv : wp_reals.
#[export] Hint Resolve Rabs_def1 : wp_reals.
#[export] Hint Resolve Rabs_le : wp_reals.
#[export] Hint Resolve Rabs_left : wp_reals.
#[export] Hint Resolve Rabs_minus_sym : wp_reals.
#[export] Hint Resolve Rabs_right : wp_reals.
#[export] Hint Resolve Rabs_left1 : wp_reals.
#[export] Hint Resolve Rabs_left1_with_minus : wp_reals.
#[export] Hint Resolve Rabs_pos_lt : wp_reals.
#[export] Hint Resolve Rabs_Rabsolu : wp_reals.
#[export] Hint Resolve Rabs_zero : wp_reals.
#[export] Hint Resolve Rle_abs : wp_reals.
#[export] Hint Resolve Rabs_pos : wp_reals.
#[export] Hint Resolve Rle_abs_min : wp_reals.
#[export] Hint Resolve Rge_min_abs : wp_reals.
#[export] Hint Resolve Rmax_abs : wp_reals.
#[export] Hint Resolve Rinv_0_lt_compat : wp_reals.
#[export] Hint Resolve Rplus_lt_compat : wp_reals.
#[export] Hint Resolve Rplus_lt_le_compat : wp_reals.

#[export] Hint Extern 1 => rewrite Rabs_zero : wp_reals.

End wp_reals.

Module wp_subsets <: preloader.

Import Waterproof.theory.logic_and_set_theory.subsets.

#[export] Hint Resolve left_in_closed_open left_in_closed_open : wp_subsets.

End wp_subsets.

Module wp_sets <: preloader.

Import Sets.Ensembles.
Import Sets.Classical_sets.
Import Waterproof.tactics.sets_tactics.sets_automation_tactics.

#[export] Hint Constructors Union Intersection Disjoint Full_set : wp_sets.
(** Would like to add the following hint, but this undesirably interferes with workings of the other automation
    tactics. Also, what weight to use? *)
#[export] Hint Extern 5 (_ = _) => try (ltac2:(trivial_set_equality ())) : wp_sets.

End wp_sets.

Module wp_all <: preloader.

Export wp_classical_logic.
Export wp_constructive_logic.
Export wp_core.
Export wp_decidability_classical.
Export wp_decidability_nat.
Export wp_decidability_reals.
Export wp_eq_abs.
Export wp_eq_exp.
Export wp_eq_minus.
Export wp_eq_mult.
Export wp_eq_one.
Export wp_eq_opp.
Export wp_eq_plus.
Export wp_eq_sqr.
Export wp_eq_zero.
Export wp_firstorder.
Export wp_integers.
Export wp_intuition.
Export wp_negation_int.
Export wp_negation_nat.
Export wp_negation_reals.
Export wp_reals.
Export wp_subsets.
Export wp_sets.

End wp_all.
