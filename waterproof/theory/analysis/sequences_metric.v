From Ltac2 Require Import Ltac2.
Require Import Waterproof.tactics.unfold.

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

Declare Scope metric_scope.
Notation "a ⟶ c" := (convergence a c) (at level 20) : metric_scope.


Local Ltac2 unfold_convergence    ()          := unfold convergence.
Local Ltac2 unfold_convergence_in (h : ident) := unfold convergence in $h.
Ltac2 Notation "Expand" "the" "definition" "of" "⟶" cl(opt(seq("in", "(", ident, ")"))) := 
  expand_def_framework unfold_convergence unfold_convergence_in cl.

(* For some reason coq does not like the symbol ⟶ in the Ltac2 notation.*)
(* Using the above tactic reurns the following error:
    Syntax error: [q_reference] expected after 'of' (in [ltac2_expr]). *)
(* With -->, waterproof complains, giving the following error:
    Command not supported (No proof-editing in progress)*)

Close Scope R_scope.