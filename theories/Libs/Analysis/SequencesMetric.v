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

Require Import Automation.
Require Import Libs.Negation.
Require Import Notations.
Require Import Tactics.

Waterproof Enable Automation RealsAndIntegers.

Open Scope R_scope.

(** * Sequences in metric spaces *)
(** * TODO change the naming in this file *)
Definition convergence {M : Metric_Space}
                       (a : ℕ → Base M)
                       (c : Base M) :=
  ∀ ε : ℝ, ε > 0 ⇒
    ∃ N1 : ℕ, ∀ n : ℕ, (n ≥ N1)%nat ⇒
      dist M (a n) c < ε.

Definition bounded {X : Metric_Space} (a : ℕ → Base X) :=
  ∃ q : Base X,
    ∃ M : ℝ, M > 0 ⇒
      ∀ n : ℕ, dist X (a n) q ≤ M.

Declare Scope metric_scope.
Notation "a ⟶ c" := (convergence a c) (at level 20) : metric_scope.
Local Ltac2 unfold_convergence (statement : constr) := eval unfold convergence in $statement.
Ltac2 Notation "Expand" "the" "definition" "of" "⟶" "in" statement(constr) := 
  unfold_in_statement unfold_convergence (Some "⟶") statement.
Ltac2 Notation "_internal_" "Expand" "the" "definition" "of" "⟶" "in" statement(constr) := 
  unfold_in_statement_no_error unfold_convergence (Some "⟶") statement.

(* With -->, waterproof complains, giving the following error:
    Command not supported (No proof-editing in progress)*)

Notation "a '_converges' 'to_' p" := (convergence a p) (at level 68) : metric_scope.
Notation "a 'converges' 'to' p" := (convergence a p) (at level 68, only parsing) : metric_scope.
Ltac2 Notation "Expand" "the" "definition" "of" "converges" "to" "in" statement(constr) := 
  unfold_in_statement unfold_convergence (Some "converges to") statement.
Ltac2 Notation "_internal_" "Expand" "the" "definition" "of" "converges" "to" "in" statement(constr) := 
  unfold_in_statement_no_error unfold_convergence (Some "converges to") statement.

(* Index shift*)
Lemma relation_shift {X : Metric_Space} (a : nat -> Base X) (k : nat) (n : nat) (n_ge_k : (n ≥ k)%nat) : 
  a ((n - k) + k)%nat = a n.
Proof.
We conclude that (a (n - k + k) = a n)%nat.
Qed.

#[export] Hint Resolve relation_shift : wp_integers.
#[export] Hint Extern 1 (_ = _) => (rewrite relation_shift) : wp_integers.

Close Scope R_scope.
