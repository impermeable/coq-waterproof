(** * Populate Waterproof reals database

Authors:
    - Jim Portegies
    - Jelle Wemmenhove

Creation date: 26 Mar 2023.

This file populates the reals database.

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

(** ** Populate the Waterproof reals database *)

Require Import Reals.
Require Import Coq.micromega.Lra.
Require Import Waterproof.tactics.simplify_chains.
Require Import Waterproof.waterprove.simplify_subsets.
Require Import Waterproof.theory.analysis.reals.

#[export] Hint Extern 3 => ltac2:(simpl_member_subset ()); lra : reals. (*TODO: do we need a hint database for (reals-and-subsets)?*)
(* #[export] Hint Extern 3 => ltac2:(simpl_member_subset ()); lia : waterproof_integers. (* not yet needed? *) *)
#[export] Hint Extern 3 (pred R _ _) => simpl; lra : reals.

#[export] Hint Extern 3 ( @eq R _ _ ) => ltac2:(simpl_ineq_chains ()); field : reals.

#[export] Hint Extern 3 ( Rle _ _ ) => cbn; ltac2:(simpl_ineq_chains ()); lra : reals.
#[export] Hint Extern 3 ( Rge _ _ ) => cbn; ltac2:(simpl_ineq_chains ()); lra : reals.
#[export] Hint Extern 3 ( Rlt _ _ ) => cbn; ltac2:(simpl_ineq_chains ()); lra : reals.
#[export] Hint Extern 3 ( Rgt _ _ ) => cbn; ltac2:(simpl_ineq_chains ()); lra : reals.

#[export] Hint Extern 3 (~ (Rle _ _) ) => cbn; ltac2:(simpl_ineq_chains ()); lra : reals.
#[export] Hint Extern 3 (~ (Rge _ _) ) => cbn; ltac2:(simpl_ineq_chains ()); lra : reals.
#[export] Hint Extern 3 (~ (Rlt _ _) ) => cbn; ltac2:(simpl_ineq_chains ()); lra : reals.
#[export] Hint Extern 3 (~ (Rgt _ _) ) => cbn; ltac2:(simpl_ineq_chains ()); lra : reals.
#[export] Hint Extern 3 (~ (@eq R _ _ ) ) => cbn; ltac2:(simpl_ineq_chains ()); lra : reals.

#[export] Hint Extern 3 ( Rle _ _ ) => cbn; nra : reals.
#[export] Hint Extern 3 ( Rge _ _ ) => cbn; nra : reals.
#[export] Hint Extern 3 ( Rlt _ _ ) => cbn; nra : reals.
#[export] Hint Extern 3 ( Rgt _ _ ) => cbn; nra : reals.

#[export] Hint Resolve eq_sym : reals.
#[export] Hint Resolve false_Req : reals.
#[export] Hint Resolve true_Req : reals.

#[export] Hint Resolve Rmin_l : reals.
#[export] Hint Resolve Rmin_r : reals.
#[export] Hint Resolve Rmax_l : reals.
#[export] Hint Resolve Rmax_r : reals.
#[export] Hint Resolve Rle_max_compat_l : reals.
#[export] Hint Resolve Rle_max_compat_r : reals.
#[export] Hint Resolve Rmax_lub : reals.
#[export] Hint Resolve Rmax_lub_lt : reals.
#[export] Hint Resolve Rmax_left : reals.
#[export] Hint Resolve Rmax_right : reals.
#[export] Hint Resolve Rmin_left : reals.
#[export] Hint Resolve Rmin_right : reals.
#[export] Hint Resolve Rmin_glb : reals.
#[export] Hint Resolve Rmin_glb_lt : reals.

#[export] Hint Resolve div_sign_flip : reals.
#[export] Hint Resolve div_pos : reals.
#[export] Hint Resolve inv_remove : reals.
#[export] Hint Resolve Rinv_inv : reals.
#[export] Hint Resolve Rabs_def1 : reals.
#[export] Hint Resolve Rabs_le : reals.
#[export] Hint Resolve Rabs_left : reals.
#[export] Hint Resolve Rabs_right : reals.
#[export] Hint Resolve Rabs_left1 : reals.
#[export] Hint Resolve Rabs_left1_with_minus : reals.
#[export] Hint Resolve Rabs_pos_lt : reals.
#[export] Hint Resolve Rabs_zero : reals.
#[export] Hint Resolve Rle_abs : reals.
#[export] Hint Resolve Rabs_pos : reals.
#[export] Hint Resolve Rle_abs_min : reals.
#[export] Hint Resolve Rge_min_abs : reals.
#[export] Hint Resolve Rmax_abs : reals.
#[export] Hint Resolve Rinv_0_lt_compat : reals.

#[export] Hint Extern 1 => rewrite Rabs_zero : reals.
