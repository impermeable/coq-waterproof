Set Default Goal Selector "!".
Set Default Timeout 5.

Require Import Reals.
Require Import Waterproof.AllTactics.
Require Import Waterproof.notations.notations.
Require Import Waterproof.load_database.RealsAndIntegers.
Require Import Waterproof.set_search_depth.To_5.
Require Import Waterproof.theory.analysis.open_and_closed.

Open Scope R_scope.
Open Scope subset_scope.


Goal (¬ [0,1) is closed).
Proof.
  Expand the definition of closed.
  That is, write the goal as (¬ ℝ\[0,1) is open).
  Expand the definition of open.
  That is, write the goal as 
    (¬ ∀ a : ℝ, a : ℝ\[0,1) ⇒ a is an interior point of ℝ\[0,1)).
  It suffices to show that
    (∃ a : ℝ, a : ℝ\[0,1) ∧ ¬ a is an interior point of ℝ\[0,1)).
  Choose a := 1.
  We show both statements.
  - We conclude that (1 : ℝ\[0,1)).
  - We need to show that (¬ 1 is an interior point of ℝ\[0,1)).
    Expand the definition of interior point.
    That is, write the goal as
      (¬ ∃ r : ℝ, r > 0 ∧ (∀ x : ℝ, x : B(1,r) ⇒ x : ℝ\[0,1))).
    It suffices to show that
      (∀ r : ℝ, r > 0 ⇒ (∃ x : ℝ, x : B(1,r) ∧ x : [0,1))).
    Take r : ℝ. Assume that (r > 0).
    Choose x := (Rmax(1/2, 1 - r/2)).
    We show both (x : B(1,r)) and (x : [0,1)).
    + We need to show that (| x - 1 | < r).
      It suffices to show that (-r < x - 1 < r).
      We show both (-r < x - 1) and (x - 1 < r).
      * It holds that (1 - r/2 ≤ Rmax(1/2, 1 - r/2)).
        We conclude that (& -r < -r/2 = 1 - r/2 - 1 ≤ Rmax(1/2, 1 - r/2) - 1 = x - 1).
      * We conclude that (& x - 1 = Rmax(1/2, 1 - r/2) - 1 < 0 < r).
    + We need to show that (x : [0,1)).
      We need to show that (0 ≤ x ∧ x < 1).
      We show both (0 ≤ x) and (x < 1).
      * We conclude that (& 0 ≤ 1/2 ≤ Rmax(1/2, 1 - r/2) = x).
      * We conclude that (& x = Rmax(1/2, 1 - r/2) < 1).
Qed.

Close Scope R_scope.
Close Scope subset_scope.
