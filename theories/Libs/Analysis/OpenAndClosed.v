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

From Stdlib Require Import Reals.Reals.
From Stdlib Require Import Classical_Prop.

Require Import Automation.
Require Import Notations.Common.
Require Import Notations.Reals.
Require Import Notations.Sets.
Require Import Tactics.

Waterproof Enable Automation RealsAndIntegers.

Open Scope R_scope.
Open Scope subset_scope.

(** Definitions *)
Definition open_ball (p : R) (r : R) : subset R := as_subset _ (fun x => | x - p | < r).

Definition is_interior_point (a : R) (A : R -> Prop) :=
  ∃ r > 0, ∀ x ∈ (open_ball a r), x ∈ A.

Definition is_open (A : R -> Prop) := ∀ a ∈ A, is_interior_point a A.

Definition complement (A : R -> Prop) : subset R := as_subset _ (fun x => not (A x)).

Definition is_closed (A : R -> Prop) := is_open (complement A).


(** Notations *)
Notation "B( p , r )" := (open_ball p r) (at level 68, format "B( p ,  r )").

Waterproof Register Expand "B";
  for open_ball;
  as "Definition open ball".

Waterproof Register Expand "open" "ball";
  for open_ball;
  as "Definition open ball".

Notation "a 'is' 'an' '_interior' 'point_' 'of' A" := (is_interior_point a A) (at level 69).

Notation "a 'is' 'an' 'interior' 'point' 'of' A" := (is_interior_point a A) (at level 69, only parsing).

Waterproof Register Expand "interior" "point";
  for is_interior_point;
  as "Definition interior point".

Notation "A 'is' '_open_'" := (is_open A) (at level 69).

Notation "A 'is' 'open'" := (is_open A) (at level 69, only parsing).

Waterproof Register Expand "open";
  for is_open;
  as "Definition open".

Notation "'ℝ\' A" := (complement A) (at level 20, format "'ℝ\' A").

Notation "'ℝ' '\' A" := (complement A) (at level 0, only parsing).

Waterproof Register Expand "complement";
  for complement;
  as "Definition complement".

Waterproof Register Expand "ℝ\";
  for complement;
  as "Definition complement".

Notation "A 'is' '_closed_'" := (is_closed A) (at level 69).

Notation "A 'is' 'closed'" := (is_closed A) (at level 69, only parsing).

Waterproof Register Expand "closed";
  for is_closed;
  as "Definition closed".

(** Hints *)
Lemma zero_in_interval_closed_zero_open_one : (0 ∈ [0,1)).
Proof.
  We need to show that 0 <= 0 /\ 0 < 1.
  We show both 0 <= 0 and 0 < 1.
  - We conclude that 0 <= 0.
  - We conclude that 0 < 1.
Qed.
#[export] Hint Resolve zero_in_interval_closed_zero_open_one : wp_reals.

Lemma one_in_complement_interval_closed_zero_open_one : (1 ∈ ℝ \ [0,1)).
Proof.
  We need to show that ~ ((0 <= 1) /\ (1 < 1)).
  We conclude that ¬ 0 <= 1 < 1.
Qed.

#[export] Hint Resolve one_in_complement_interval_closed_zero_open_one : wp_reals.
#[export] Hint Resolve Rabs_def1 : wp_reals.
#[export] Hint Resolve not_and_or : wp_classical_logic.

Lemma not_in_compl_implies_in (A : subset ℝ) (x : ℝ) : (¬ x ∈ ℝ\A) -> (x ∈ A).
Proof.
  Assume that ¬ x ∈ ℝ\A.
  It holds that ¬ ¬ x ∈ A.
  We conclude that x ∈ A.
Qed.

Lemma in_implies_not_in_compl (A : subset R) (x : R) : (x ∈ A) -> (¬ x ∈ ℝ\A).
Proof.
  Assume that x ∈ A.
  We conclude that ¬ x ∈ ℝ\A.
Qed.

#[export] Hint Resolve not_in_compl_implies_in : wp_negation_reals.
#[export] Hint Resolve in_implies_not_in_compl : wp_negation_reals.

Close Scope subset_scope.
Close Scope R_scope.
