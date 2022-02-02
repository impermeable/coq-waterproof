Set Default Goal Selector "!".
Set Default Timeout 5.

Require Import Reals.
Require Import Waterproof.AllTactics.
Require Import Waterproof.notations.notations.
Require Import Waterproof.load_database.RealsAndIntegers.
Require Import Waterproof.set_search_depth.To_5.
Global Hint Resolve Rabs_def1 : reals.
Global Hint Resolve Rmax_lub_lt : reals.


Definition open_ball (p : ℝ) (r : ℝ) := mk_subset_R (fun x => | x - p | < r).

Definition is_interior_point (a : ℝ) (A : subset_R) 
:= there exists r : ℝ, (r > 0) ∧ (for all x : ℝ, (open_ball a r) x ⇒ A x).

Definition is_open (A : subset_R) := for all a : ℝ, A a ⇒ is_interior_point a A.

Definition complement (A : subset_R) := mk_subset_R (x ↦ (¬ (A x))).
Notation "A ^c" := (complement A) (at level 9).

Definition is_closed (A : subset_R) := is_open A^c.


Lemma zero_in_interval_closed_zero_open_one : ([0,1) 0).
Proof.
  We need to show that (0 ≤ 0 ∧ 0 < 1).
  We show both (0 ≤ 0) and (0 < 1).
  - We conclude that (0 ≤ 0).
  - We conclude that (0 < 1).
Qed.
Global Hint Resolve zero_in_interval_closed_zero_open_one : reals.

Lemma one_in_complement_interval_closed_zero_open_one : ([0,1)^c 1).
Proof.
  We need to show that (¬ ((0 ≤ 1) ∧ (1 < 1))).
  It suffices to show that (¬ 1 < 1).
  We conclude that (¬ 1 < 1).
Qed.
Global Hint Resolve one_in_complement_interval_closed_zero_open_one : reals.

Goal (¬ is_open [0,1)).
Proof.
  Assume that (is_open [0,1)).
  It holds that ([0,1) 0).
  It holds that (is_interior_point 0 [0,1)) (i).
  Obtain r according to (i), so for r : ℝ it holds that
    (r > 0 ∧ (for all x : ℝ, (open_ball 0 r) x ⇒ [0,1) x)) (ii).
  Because (ii) both (r > 0) and 
    (for all x : ℝ, (open_ball 0 r) x ⇒ [0,1) x) (iii) hold.
  It holds that ( | -r/2 - 0 | < r).
  It holds that ((open_ball 0 r) (-r/2)).
  By (iii) it holds that ([0,1) (-r/2)) (iv).
  Because (iv) both (0 ≤ -r/2) and (-r/2 < 1) hold.
  It holds that (¬ r > 0).
  Contradiction.
Qed.

Goal (¬ is_closed [0,1)).
Proof.
  We need to show that 
    (¬ (for all a : ℝ, ([0,1)^c a) ⇒ is_interior_point a [0,1)^c)).
  It suffices to show that
    (there exists a : ℝ, ([0,1)^c a) ∧ ¬(is_interior_point a [0,1)^c)).
  Choose a := 1.
  We show both statements.
  - We need to show that ([0,1)^c 1).
    We conclude that ([0,1)^c 1).
  - We need to show that (¬(is_interior_point 1 [0,1)^c)).
    We need to show that 
      (¬ there exists r : ℝ, r > 0 ∧ (for all x : ℝ, open_ball 1 r x ⇒ [0,1)^c x)).
    It suffices to show that
      (for all r : ℝ, r > 0 ⇒ (there exists x : ℝ, (open_ball 1 r x) ∧ (¬ [0,1)^c x))).
    Take r : R. Assume that (r > 0).
    Choose x := (Rmax (1/2) (1 - r/2)).
    We show both (open_ball 1 r x) and (¬[0,1)^c x).
    + We need to show that (| x - 1 | < r).
      It suffices to show that (-r < x - 1 < r).
      We show both (-r < x - 1) and (x - 1 < r).
      * It holds that (1 - r/2 ≤ (Rmax (1/2) (1 - r/2))).
        We conclude that (& -r &< -r/2 &= 1 - r/2 - 1 &≤ (Rmax (1/2) (1-r/2)) - 1 &= x - 1).
      * We conclude that (& x - 1 &= Rmax (1/2) (1 - r/2) - 1 &< 0 &< r).
    + We need to show that (¬ [0,1)^c x).
      It suffices to show that ([0,1) x).
      We need to show that (0 ≤ x ∧ x < 1).
      We show both (0 ≤ x) and (x < 1).
      * We conclude that (& 0 &≤ 1/2 &≤ Rmax (1/2) (1 - r/2) &= x).
      * We conclude that (& x &= Rmax (1/2) (1 - r/2) &< 1).
Qed.
