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
    ∃ N : ℕ, ∀ n : ℕ, (n ≥ N)%nat ⇒
      dist M (a n) c < ε.

Definition bounded {X : Metric_Space} (a : ℕ → Base X) :=
  ∃ q : Base X,
    ∃ M : ℝ, M > 0 ⇒
      ∀ n : ℕ, dist X (a n) q ≤ M.

Declare Scope metric_scope.
Notation "a ⟶ c" := (convergence a c) (at level 20) : metric_scope.
Local Ltac2 unfold_convergence    ()          := unfold convergence.
Local Ltac2 unfold_convergence_in (h : ident) := unfold convergence in $h.
Ltac2 Notation "Expand" "the" "definition" "of" "⟶" cl(opt(seq("in", "(", ident, ")"))) := 
  expand_def_framework unfold_convergence unfold_convergence_in cl.

(* With -->, waterproof complains, giving the following error:
    Command not supported (No proof-editing in progress)*)

Notation "a '_converges' 'to_' p" := (convergence a p) (at level 68) : metric_scope.
Notation "a 'converges' 'to' p" := (convergence a p) (at level 68, only parsing) : metric_scope.
Ltac2 Notation "Expand" "the" "definition" "of" "converges" "to" cl(opt(seq("in", "(", ident, ")"))) := 
  expand_def_framework unfold_convergence unfold_convergence_in cl.

(* Index shift*)
Lemma relation_shift {X : Metric_Space} (a : nat -> Base X) (k : nat) (n : nat) (n_ge_k : (n ≥ k)%nat) : 
  a ((n - k) + k)%nat = a n.
Proof.
We conclude that (a (n - k + k) = a n)%nat.
Qed.

#[export] Hint Resolve relation_shift : wp_integers.
#[export] Hint Extern 1 (_ = _) => (rewrite relation_shift) : wp_integers.

Close Scope R_scope.
