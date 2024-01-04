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
Require Import Ltac2.Ltac2.

Require Import Waterproof.Waterproof.
Require Import Waterproof.Automation.
Require Import Waterproof.Notations.
Require Import Waterproof.Waterprove.

Waterproof Enable Automation RealsAndIntegers.

Open Scope R_scope.

Goal forall x y: R, forall f: R -> R, x = y -> f (x + 1) = f (y + 1).
Proof.
  waterprove 5 false Main.
Qed.

Goal forall x y: R, forall f: R -> R, x = y -> f x = f y /\ x = y.
Proof.
  waterprove 5 false Main.
Qed.

Goal (& 3 < 4 <= 5).
  cbn; repeat split; auto with wp_core wp_reals.
Qed.

Goal (& 3 = 3 = 3).
  cbn; repeat split; auto with wp_core wp_reals.
Qed.

Goal forall x : R, (& x < 5 = 2 + 3) -> (x < 5).
  intro x.
  intro H.
  auto with wp_core wp_reals.
Qed.

(** ** Testcases to deal with Rabs Rmin Rmax *)

Goal forall b: R, b > 0 -> - Rmax( 0, 1 - b/2) >= - 1.
  auto with wp_reals.
Qed.

Goal forall b: R, b > 0 -> Rmin( 0, -1 + b/2) <= 1.
  auto with wp_reals.
Qed.

Goal forall r : R, r > 0 ->
  | Rmax 0 (1 - r/2) - 1 | = 1 - (Rmax 0 (1 - r/2)).
  auto with wp_reals.
Qed.

Goal forall x r : R, r > 0 ->
  x = Rmax 0 (1 - r/2) -> Rabs (x - 1) < r.
  intros x r r_gt_0 x_eq_Rmax.
  auto with wp_reals.
Qed.

Close Scope R_scope.
