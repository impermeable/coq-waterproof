Require Import Ltac2.Ltac2.

Require Export Util.Goals.

Ltac2 Type exn ::= [ BothDirectionsError(string) ].

(**
  Split the proof of an if and only if statement into both of its directions, wraps both resulting goals in a [StateGoal.Wrapper].

  Arguments:
    - no arguments

  Does:
    - splits the if and only if statement into its both directions.
    - wraps both goals in a [StateGoal.Wrapper].

  Raises Exceptions:
    - [BothDirectionsError], if the [goal] is not an if and only if [goal].
*)
Ltac2 both_statements_iff () :=
  lazy_match! goal with 
    | [ |- _ <-> _] => split; Control.enter (fun () => apply StateGoal.unwrap)
    | [ |- _ ] => Control.zero (BothDirectionsError "The goal is not to show an `if and only if`-statement, try another tactic.")
  end.

Ltac2 Notation "We" "show" "both" "directions" := 
  panic_if_goal_wrapped ();
  both_statements_iff ().

Ltac2 Notation "We" "prove" "both" "directions" := 
  panic_if_goal_wrapped ();
  both_statements_iff ().
