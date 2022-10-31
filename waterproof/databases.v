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

(** ** Logic database *) 

(** ## De Morgan laws for quantifiers according to classical logic *)
Require Import Classical_Pred_Type.

Global Hint Resolve not_ex_all_not : constructive_logic.
Global Hint Resolve ex_not_not_all : constructive_logic.
Global Hint Resolve all_not_not_ex : constructive_logic.

Global Hint Resolve not_ex_all_not : classical_logic.
Global Hint Resolve ex_not_not_all : classical_logic.
Global Hint Resolve all_not_not_ex : classical_logic.
Global Hint Resolve not_all_not_ex : classical_logic.
Global Hint Resolve not_all_ex_not : classical_logic.
(* not_ex_not_all cannot be used as a hint. *)
(* Global Hint Resolve not_ex_not_all : classical_logic. *)

Open Scope R_scope.

(* subsets *)
Global Hint Extern 3 => ltac2:(simpl_member_subset ()); lra : reals. (*TODO: do we need a hint database for (reals-and-subsets)?*)
(* Global Hint Extern 3 => ltac2:(simpl_member_subset ()); lia : waterproof_integers. (* not yet needed? *) *)
Global Hint Extern 3 (pred R _ _) => simpl; lra : reals.

Open Scope subset_scope.
Lemma left_in_closed_open {a b : R} : (a < b) -> (a : [a,b)).
Proof.
  intro a_lt_b.
  split.
  - apply Rle_refl.
  - exact a_lt_b.
Qed.
Lemma right_in_open_closed {a b : R} : (a < b) -> (b : (a,b]).
Proof.
  intro a_lt_b.
  split.
  - exact a_lt_b.
  - apply Rle_refl.
Qed.
Global Hint Resolve left_in_closed_open left_in_closed_open : subsets.
Close Scope subset_scope.


(** *** The reals database *)
Lemma Req_true : forall x y : R, x = y -> Reqb x y = true.
Proof.
    intros. 
    destruct (Reqb_eq x y). 
    apply (H1 H).
Qed.

Lemma true_Req : forall x y : R, Reqb x y = true -> x = y.
Proof.
    intros.
    destruct (Reqb_eq x y). 
    apply (H0 H).
Qed.

Lemma Req_false : forall x y : R, x <> y -> Reqb x y = false.
Proof.
    intros. 
    unfold Reqb. 
    destruct Req_dec. 
    contradiction. 
    trivial.
Qed.

Lemma false_Req : forall x y : R, Reqb x y = false -> x <> y.
Proof.
    intros. 
    destruct (Req_dec x y). 
    rewrite (Req_true x y e) in H. 
    assert (H1 : true <> false). 
    auto with *. 
    contradiction.
    apply n.
Qed.

(* Hint to solve inequality chains. Redundant when using the waterprove subroutine. *)
Global Hint Extern 0 (total_statement _) => repeat split; cbn : core.

Global Hint Resolve eq_sym : reals.
Global Hint Resolve false_Req : reals.
Global Hint Resolve true_Req : reals.

(** TODO: find a different solution for the simplification of inequality chains? *)
Global Hint Extern 3 ( @eq R _ _ ) => ltac2:(simpl_ineq_chains ()); field : reals.

Global Hint Extern 3 ( Rle _ _ ) => cbn; ltac2:(simpl_ineq_chains ()); lra : reals.
Global Hint Extern 3 ( Rge _ _ ) => cbn; ltac2:(simpl_ineq_chains ()); lra : reals.
Global Hint Extern 3 ( Rlt _ _ ) => cbn; ltac2:(simpl_ineq_chains ()); lra : reals.
Global Hint Extern 3 ( Rgt _ _ ) => cbn; ltac2:(simpl_ineq_chains ()); lra : reals.

Global Hint Extern 3 (~ (Rle _ _) ) => cbn; ltac2:(simpl_ineq_chains ()); lra : reals.
Global Hint Extern 3 (~ (Rge _ _) ) => cbn; ltac2:(simpl_ineq_chains ()); lra : reals.
Global Hint Extern 3 (~ (Rlt _ _) ) => cbn; ltac2:(simpl_ineq_chains ()); lra : reals.
Global Hint Extern 3 (~ (Rgt _ _) ) => cbn; ltac2:(simpl_ineq_chains ()); lra : reals.
Global Hint Extern 3 (~ (@eq R _ _ ) ) => cbn; ltac2:(simpl_ineq_chains ()); lra : reals.

Global Hint Extern 3 ( Rle _ _ ) => cbn; nra : reals.
Global Hint Extern 3 ( Rge _ _ ) => cbn; nra : reals.
Global Hint Extern 3 ( Rlt _ _ ) => cbn; nra : reals.
Global Hint Extern 3 ( Rgt _ _ ) => cbn; nra : reals.

Global Hint Extern 3 ( _ = _ ) => cbn; ltac2:(simpl_ineq_chains ()); ring : waterproof_integers.
Global Hint Extern 3 ( @eq nat _  _) => cbn; ltac2:(simpl_ineq_chains ()); lia : waterproof_integers.
Global Hint Extern 3 ( le _ _ ) => cbn; ltac2:(simpl_ineq_chains ()); lia : waterproof_integers.
Global Hint Extern 3 ( ge _ _ ) => cbn; ltac2:(simpl_ineq_chains ()); lia : waterproof_integers.
Global Hint Extern 3 ( lt _ _ ) => cbn; ltac2:(simpl_ineq_chains ()); lia : waterproof_integers.
Global Hint Extern 3 ( gt _ _ ) => cbn; ltac2:(simpl_ineq_chains ()); lia : waterproof_integers.

Global Hint Resolve Rmin_l : reals.
Global Hint Resolve Rmin_r : reals.
Global Hint Resolve Rmax_l : reals.
Global Hint Resolve Rmax_r : reals.
Global Hint Resolve Rle_max_compat_l : reals.
Global Hint Resolve Rle_max_compat_r : reals.
Global Hint Resolve Rmax_lub : reals.
Global Hint Resolve Rmax_lub_lt : reals.
Global Hint Resolve Rmax_left : reals.
Global Hint Resolve Rmax_right : reals.
Global Hint Resolve Rmin_left : reals.
Global Hint Resolve Rmin_right : reals.
Global Hint Resolve Rmin_glb : reals.
Global Hint Resolve Rmin_glb_lt : reals.

(** ## Lemmas regarding identities for absolute values and inverses*)
Lemma div_sign_flip : forall r1 r2 : R, r1 > 0 -> r2 > 0 -> r1 > 1 / r2 -> 1 / r1 < r2.
Proof.
    intros.
    unfold Rdiv in *.
    rewrite Rmult_1_l in *.
    rewrite <- (Rinv_involutive r2).
    apply (Rinv_lt_contravar (/ r2) r1).
    apply Rmult_lt_0_compat. 
    apply Rinv_0_lt_compat. 
    apply H0. 
    apply H.
    apply H1. 
    apply Rgt_not_eq. 
    apply H0.
Qed.

Lemma div_pos : forall r1 r2 : R, r1 > 0 ->1 / r1 > 0.
Proof.
    intros. 
    unfold Rdiv. 
    rewrite Rmult_1_l. 
    apply Rinv_0_lt_compat. 
    apply H.
Qed.

Lemma Rabs_zero : forall r : R, Rabs (r - 0) = Rabs r.
Proof.
    intros. 
    rewrite Rminus_0_r. 
    trivial.
Qed.

Lemma inv_remove : forall r1 r2 : R, 0 < r1 -> 0 < r2 -> 1 / r1 < 1 / r2 -> r1 > r2.
Proof.
    intros.
    unfold Rdiv in *. 
    rewrite Rmult_1_l in *.
    rewrite <- (Rinv_involutive r1), <- (Rinv_involutive r2).
    apply (Rinv_lt_contravar (/ r1) (/ r2)). 
    apply Rmult_lt_0_compat. 
    apply Rinv_0_lt_compat. 
    apply H.
    apply Rinv_0_lt_compat. 
    apply H0. 
    rewrite Rmult_1_l in *. 
    apply H1.
    all: apply Rgt_not_eq; assumption.
Qed.

Lemma Rle_abs_min : forall x : R, -x <= Rabs x.
Proof.
    intros. 
    rewrite <- (Rabs_Ropp (x)). 
    apply Rle_abs.
Qed.

Lemma Rge_min_abs : forall x : R, x >= -Rabs x.
Proof.
    intros. 
    rewrite <- (Ropp_involutive x). 
    apply Ropp_le_ge_contravar.
    rewrite (Rabs_Ropp (- x)). 
    apply Rle_abs.
Qed.

Lemma Rmax_abs : forall a b : R, Rmax (Rabs a) (Rabs b) >= 0.
Proof.
    intros.
    apply (Rge_trans _ (Rabs a) _).
    apply Rle_ge.
    apply Rmax_l.
    apply (Rle_ge 0 (Rabs a)).
    apply Rabs_pos.
Qed.


Global Hint Resolve div_sign_flip : reals.
Global Hint Resolve div_pos : reals.
Global Hint Resolve inv_remove : reals.
Global Hint Resolve Rinv_involutive : reals.
Global Hint Resolve Rabs_left : reals.
Global Hint Resolve Rabs_right : reals.
Global Hint Resolve Rabs_left1 : reals.
Global Hint Resolve Rabs_pos_lt : reals.
Global Hint Resolve Rabs_zero : reals.
Global Hint Resolve Rle_abs : reals.
Global Hint Resolve Rabs_pos : reals.
Global Hint Resolve Rle_abs_min : reals.
Global Hint Resolve Rge_min_abs : reals.
Global Hint Resolve Rmax_abs : reals.
Global Hint Resolve Rinv_0_lt_compat : reals.

Global Hint Extern 1 => rewrite Rabs_zero : reals.

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
Global Hint Extern 1 => (rewrite Rinv_involutive) : eq_one. (* / / x = x *)






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
Global Hint Resolve le_not_lt : negation_nat.
Global Hint Resolve lt_not_le : negation_nat.
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

(** Lemmas to write e.g. `{r1 ≤ r2} + {r2 < r1}`.*)
Global Hint Resolve Rlt_le_dec : decidability_reals.
Lemma Rlt_ge_dec : forall r1 r2, {r1 < r2} + {r1 >= r2}.
Proof.
    intros.
    destruct (total_order_T r1 r2). 
    destruct s.
    exact (left r).
    exact (right (Req_ge r1 r2 e)). 
    exact (right (Rle_ge r2 r1 (Rlt_le r2 r1 r))).
Qed.
Global Hint Resolve Rlt_ge_dec : decidability_reals.

(** Lemmas to write e.g. `{r1 ≤ r2} + {~r2 ≥ r1}`.*)
Global Hint Resolve Rlt_dec Rle_dec Rge_dec : decidability_reals.
Lemma Rle_ge_dec : forall r1 r2, {r1 <= r2} + {~ r2 >= r1}.
Proof.
    intros.
    destruct (total_order_T r1 r2).
    destruct s.
    ltac1:(apply (left (Rlt_le r1 r2 r))).
    ltac1:(apply (left (Req_le r1 r2 e))).
    ltac1:(apply (right (Rlt_not_ge r2 r1 r))).
Qed.
Lemma Rge_le_dec : forall r1 r2, {r1 >= r2} + {~ r2 <= r1}.
Proof.
    intros.
    destruct (total_order_T r1 r2). 
    destruct s.
    ltac1:(apply (right (Rlt_not_le r2 r1 r))).
    ltac1:(apply (left (Req_ge r1 r2 e))).
    ltac1:(apply (left (Rgt_ge r1 r2 r))).
Qed.
Global Hint Resolve Rle_ge_dec Rge_le_dec : decidability_reals.

(** Lemmas to split e.g. `{r1 <= r2} into {r1 < r2} + {r1 = r2}`.*)
Lemma Rge_lt_or_eq_dec : forall r1 r2, (r1 >= r2) -> {r2 < r1} + {r1 = r2}.
Proof.
    intros.
    destruct (total_order_T r2 r1).
    - destruct s.
      + left. exact r.
      + right. symmetry. exact e.
    - ltac1:(exfalso).
      exact (Rlt_not_ge _ _ r H).
Qed.
Global Hint Resolve Rle_lt_or_eq_dec Rge_lt_or_eq_dec : decidability_reals.

Global Hint Resolve total_order_T : decidability_reals. (* x < y, x = y or y < x*)

(* Natural numbers *)
Global Hint Resolve Nat.eq_dec : decidability_nat. (* TODO: add more! *)

Close Scope R_scope.
