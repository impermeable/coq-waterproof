(******************************************************************************)
(*                  This file is part of Waterproof-lib.                      *)
(*                                                                            *)
(*   Waterproof-lib is free software: you can redistribute it and/or modify   *)
(*    it under the terms of the GNU General Public License as published by    *)
(*     the Free Software Foundation, either version 3 of the License, or      *)
(*                    (at your option) any later version.                     *)
(*                                                                            *)
(*     Waterproof-lib is distributed in the hope that it will be useful,      *)
(*      but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*       MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the         *)
(*               GNU General Public License for more details.                 *)
(*                                                                            *)
(*     You should have received a copy of the GNU General Public License      *)
(*   along with Waterproof-lib. If not, see <https://www.gnu.org/licenses/>.  *)
(*                                                                            *)
(******************************************************************************)

Require Import Coq.Reals.Reals.
Require Import Reals.ROrderedType.
Require Import micromega.Lra.

Require Import Tactics.
Require Import Automation.
Require Import Libs.Reals.
Require Import Notations.

Waterproof Enable Automation RealsAndIntegers.

Open Scope R_scope.

Section Definitions.
Context (X : Metric_Space).

(* Definition metric_to_base := Base. *)

Coercion Base : Metric_Space >-> Sortclass.

Definition dist_positive :
  ∀ x y : X, dist X x y ≥ 0
  := dist_pos X.

Definition dist_non_degenerate :
  ∀ x y : X, (dist X x y = 0) ⇒ (x = y). 
  Take x, y : X.
  By (proj1(_,_,(dist_refl X x y))) we conclude that (dist X x y = 0 ⇨ x = y).
Defined.

Definition dist_symmetric :
  ∀ x y : X, dist X x y = dist X y x
  := dist_sym X.

Definition dist_triangle_inequality :
  ∀ x y z : X, dist X x z ≤ dist X x y + dist X y z.
  Take x, y, z : X. 
  By (dist_tri X) we conclude that (dist X x z ≤ dist X x y + dist X y z).
Qed.

Definition dist_reflexive : ∀ x : X, dist X x x = 0.
  Take x : X.
  By (proj2(_, _, (dist_refl X x x))) we conclude that (dist X x x = 0).
Defined.

End Definitions.

(** ** Example : a discrete metric on the real line *)

Definition d_discrete_R : 
  ℝ → ℝ → ℝ := fun (x y : ℝ) => if Reqb x y then 0 else 3.

Lemma d'_eq_0 : forall x y : ℝ,
  d_discrete_R x y = 0 -> (Reqb x y) = true.
Proof.
Take x, y : ℝ.
Assume that (d_discrete_R x y = 0).
Either (x = y) or (x ≠ y).
+ Case (x = y).
  By Req_true we conclude that (Reqb x y = true).

+ Case (x ≠ y).
  It holds that ((if Reqb(x, y) then 0 else 3) = 0) (i).
  rewrite (Req_false x y H) in i.
  Contradiction.
Qed.

Lemma d'_eq_3 : forall x y : ℝ, d_discrete_R x y = 3 -> (Reqb x y) = false.
Proof.
Take x, y : ℝ. 
Assume that (d_discrete_R x y = 3).
It holds that ( (if Reqb x y then 0 else 3) = 3) (i).
Either (x = y) or (x ≠ y).
+ Case (x = y).
  rewrite (Req_true x y H) in i.
  It holds that (0 ≠ 3).
  Contradiction.
+ Case (x ≠ y).
  By Req_false we conclude that (Reqb x y = false).
Qed.

#[export] Hint Resolve d'_eq_0 : wp_reals.
#[export] Hint Resolve d'_eq_3 : wp_reals.
#[export] Hint Extern 0 => unfold d_discrete_R; rewrite Req_true; lra : wp_reals.
#[export] Hint Extern 0 => unfold d_discrete_R; rewrite Req_false; lra : wp_reals.