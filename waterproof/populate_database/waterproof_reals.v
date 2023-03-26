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

Global Hint Extern 3 => ltac2:(simpl_member_subset ()); lra : reals. (*TODO: do we need a hint database for (reals-and-subsets)?*)
(* Global Hint Extern 3 => ltac2:(simpl_member_subset ()); lia : waterproof_integers. (* not yet needed? *) *)
Global Hint Extern 3 (pred R _ _) => simpl; lra : reals.

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

Global Hint Resolve eq_sym : reals.
Global Hint Resolve false_Req : reals.
Global Hint Resolve true_Req : reals.

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

Global Hint Resolve div_sign_flip : reals.
Global Hint Resolve div_pos : reals.
Global Hint Resolve inv_remove : reals.
Global Hint Resolve Rinv_inv : reals.
Global Hint Resolve Rabs_def1 : reals.
Global Hint Resolve Rabs_le : reals.
Global Hint Resolve Rabs_left : reals.
Global Hint Resolve Rabs_right : reals.
Global Hint Resolve Rabs_left1 : reals.
Global Hint Resolve Rabs_left1_with_minus : reals.
Global Hint Resolve Rabs_pos_lt : reals.
Global Hint Resolve Rabs_zero : reals.
Global Hint Resolve Rle_abs : reals.
Global Hint Resolve Rabs_pos : reals.
Global Hint Resolve Rle_abs_min : reals.
Global Hint Resolve Rge_min_abs : reals.
Global Hint Resolve Rmax_abs : reals.
Global Hint Resolve Rinv_0_lt_compat : reals.

Global Hint Extern 1 => rewrite Rabs_zero : reals.
