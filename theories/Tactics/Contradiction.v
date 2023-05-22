Require Import Classical.
Require Import Ltac2.Ltac2.
Require Import Ltac2.Message.

Require Import Util.Goals.

(**
  Starts a proof by contradiction.

  Arguments:
    - no arguments.

  Does:
    - Replaces the goal [G] by its double negation [¬ ¬ G].
*)
Ltac2 contra () :=
  lazy_match! goal with
    | [ |- ?x] =>
      apply (NNPP $x);
      apply (ByContradiction.unwrap (not $x))
    | [ |- _] => print(of_string "Failed to start a proof by contradiction.")
  end.


(**
  Calls the Ltac1 [contradiction] tactic.

  Arguments:
    - no arguments.

  Does:
    - calls the Ltac1 [contradiction] tactic, as this tactic does not exist in Ltac2. Tries to find contradictory hypotheses to show the goal.
*)
Ltac2 contradiction () := ltac1:(contradiction).

Ltac2 Notation "We" "argue" "by" "contradiction" := contra ().

Ltac2 Notation "Contradiction" := contradiction ().

Ltac2 Notation "↯" := contradiction ().