Require Import Waterproof.notations.notations.
Require Import Reals.
Open Scope R_scope.

(** * Sequences in metric spaces *)
(** * TODO change the naming in this file *)
Definition convergence {M : Metric_Space}
                       (a : ℕ → Base M)
                       (c : Base M) :=
  ∀ ε : ℝ, ε > 0 ⇒
    ∃ N : ℕ, ∀ n : ℕ, (n ≥ N)%nat ⇒
      dist M (a n) c < ε.

Definition bounded {X : Metric_Space} (a : ℕ → Base X) :=
  ∃ q : Base X,
    ∃ M : ℝ, M > 0 ⇒
      ∀ n : ℕ, dist X (a n) q ≤ M.

Notation "a ⟶ c" := (convergence a c) (at level 20) : metric_scope.