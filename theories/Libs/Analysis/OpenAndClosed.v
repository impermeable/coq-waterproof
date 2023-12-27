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
Require Import Classical_Prop.

Require Import Automation.
Require Import Notations.
Require Import Tactics.

Waterproof Enable Automation RealsAndIntegers.

Open Scope R_scope.
Open Scope subset_scope.

(** Definitions *)
Definition open_ball (p : R) (r : R) : subset R := as_subset _ (fun x => | x - p | < r).

Definition is_interior_point (a : R) (A : R -> Prop) :=
  there exists r : R, (r > 0) /\ (for all x : R, x : (open_ball a r) -> A x).

Definition is_open (A : R -> Prop) := for all a : R, A a -> is_interior_point a A.

Definition complement (A : R -> Prop) : subset R := as_subset _ (fun x => not (A x)).

Definition is_closed (A : R -> Prop) := is_open (complement A).


(** Notations *)
Notation "B( p , r )" := (open_ball p r) (at level 68, format "B( p ,  r )").

Local Ltac2 unfold_open_ball (statement : constr) := eval unfold open_ball, pred in $statement.

Ltac2 Notation "Expand" "the" "definition" "of" "B" "in" statement(constr) := 
  unfold_in_statement unfold_open_ball (Some "B") statement.
Ltac2 Notation "_internal_" "Expand" "the" "definition" "of" "B" "in" statement(constr) := 
  unfold_in_statement_no_error unfold_open_ball (Some "B") statement.

Ltac2 Notation "Expand" "the" "definition" "of" "open" "ball" "in" statement(constr) := 
  unfold_in_statement unfold_open_ball (Some "open ball ") statement.
Ltac2 Notation "_internal_" "Expand" "the" "definition" "of" "open" "ball" "in" statement(constr) := 
  unfold_in_statement_no_error unfold_open_ball (Some "open ball ") statement.

Notation "a 'is' 'an' '_interior' 'point_' 'of' A" := (is_interior_point a A) (at level 68).

Notation "a 'is' 'an' 'interior' 'point' 'of' A" := (is_interior_point a A) (at level 68, only parsing).

Local Ltac2 unfold_is_interior_point (statement : constr) := eval unfold is_interior_point in $statement.

Ltac2 Notation "Expand" "the" "definition" "of" "interior" "point" "in" statement(constr) := 
  unfold_in_statement unfold_is_interior_point (Some "interior point") statement.
Ltac2 Notation "_internal_" "Expand" "the" "definition" "of" "interior" "point" "in" statement(constr) := 
  unfold_in_statement_no_error unfold_is_interior_point (Some "interior point") statement.

Notation "A 'is' '_open_'" := (is_open A) (at level 68).

Notation "A 'is' 'open'" := (is_open A) (at level 68, only parsing).

Local Ltac2 unfold_is_open (statement : constr) := eval unfold is_open in $statement.

Ltac2 Notation "Expand" "the" "definition" "of" "open" "in" statement(constr) := 
  unfold_in_statement unfold_is_open (Some "open") statement.
Ltac2 Notation "_internal_" "Expand" "the" "definition" "of" "open" "in" statement(constr) := 
  unfold_in_statement_no_error unfold_is_open (Some "open") statement.

Notation "'ℝ\' A" := (complement A) (at level 20, format "'ℝ\' A").

Notation "'ℝ' '\' A" := (complement A) (at level 20, only parsing).

Local Ltac2 unfold_complement (statement : constr) := eval unfold complement, pred in $statement.

Ltac2 Notation "Expand" "the" "definition" "of" "ℝ\" "in" statement(constr) := 
  unfold_in_statement unfold_complement (Some "ℝ\") statement.
Ltac2 Notation "_internal_" "Expand" "the" "definition" "of" "ℝ\" "in" statement(constr) := 
  unfold_in_statement_no_error unfold_complement (Some "ℝ\") statement.

Ltac2 Notation "Expand" "the" "definition" "of" "complement" "in" statement(constr) := 
  unfold_in_statement unfold_complement (Some "complement") statement.
Ltac2 Notation "_internal_" "Expand" "the" "definition" "of" "complement" "in" statement(constr) := 
  unfold_in_statement_no_error unfold_complement (Some "complement") statement.

Notation "A 'is' '_closed_'" := (is_closed A) (at level 68).

Notation "A 'is' 'closed'" := (is_closed A) (at level 68, only parsing).

Local Ltac2 unfold_is_closed (statement : constr) := eval unfold is_closed in $statement.

Ltac2 Notation "Expand" "the" "definition" "of" "closed" "in" statement(constr) :=
  unfold_in_statement unfold_is_closed (Some "closed") statement.
Ltac2 Notation "_internal_" "Expand" "the" "definition" "of" "closed" "in" statement(constr) :=
  unfold_in_statement_no_error unfold_is_closed (Some "closed") statement.

(** Hints *)
Lemma zero_in_interval_closed_zero_open_one : (0 : [0,1)).
Proof.
  We need to show that (0 <= 0 /\ 0 < 1).
  We show both (0 <= 0) and (0 < 1).
  - We conclude that (0 <= 0).
  - We conclude that (0 < 1).
Qed.
#[export] Hint Resolve zero_in_interval_closed_zero_open_one : wp_reals.

Lemma one_in_complement_interval_closed_zero_open_one : (1 : ℝ \ [0,1)).
Proof.
  We need to show that (~ ((0 <= 1) /\ (1 < 1))).
  We conclude that (~ (& 0 <= 1 < 1)).
Qed.

#[export] Hint Resolve one_in_complement_interval_closed_zero_open_one : wp_reals.
#[export] Hint Resolve Rabs_def1 : wp_reals.
#[export] Hint Resolve not_and_or : wp_classical_logic.

Lemma not_in_compl_implies_in (A : subset ℝ) (x : ℝ) : (¬ x ∈ ℝ\A) -> (x ∈ A).
Proof.
  Assume that (¬ x : ℝ\A).
  It holds that (¬ ¬ x ∈ A).
  We conclude that (x ∈ A).
Qed.

Lemma in_implies_not_in_compl (A : subset R) (x : R) : (x ∈ A) -> (¬ x : ℝ\A).
Proof.
  Assume that (x ∈ A).
  We conclude that (¬ x : ℝ\A).
Qed.

#[export] Hint Resolve not_in_compl_implies_in : wp_negation_reals.
#[export] Hint Resolve in_implies_not_in_compl : wp_negation_reals.

Close Scope subset_scope.
Close Scope R_scope.
