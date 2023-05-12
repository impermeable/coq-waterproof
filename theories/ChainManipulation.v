From Ltac2 Require Import Ltac2.
From Ltac2 Require Option.

Require Import Waterproof.InequalityChains.

(**
  Writes out an inequality chain as a big conjunction.
*)
Ltac2 simpl_ineq_chains () :=
  repeat (
    (* TODO: do this in a more structured way *)
    match! goal with
      | [ h : total_statement _ |- _ ] => 
        cbn in $h
    end
  ).

(**
  Iteratively splits all conjunctions in the hypothesis into individual statements.
*)
Ltac2 split_conjunctions () :=
  repeat(
    match! goal with
      | [h : _ /\ _  |- _] =>
        let h_val := Control.hyp h in
        let h1 := Fresh.fresh (Fresh.Free.of_goal () ) @__wp__hl in 
        let h2 := Fresh.fresh (Fresh.Free.of_goal () ) @__wp__hr in 
        destruct $h_val as [$h1 $h2]
    end
  ).

(**
  Writes out membership of a subset [x : A] as satisfying [A]'s defining predicate [P x],
  where $A := {x : X | (P x) holds}$.
*)
Ltac2 simpl_member_subset () :=
  repeat (
    match! goal with
      | [ h : (pred _ _) _ |- _ ] => simpl in $h
      | [ |- _ ] => ()
    end
  ).