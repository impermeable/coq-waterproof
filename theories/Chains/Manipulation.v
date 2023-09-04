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

From Ltac2 Require Import Ltac2.
From Ltac2 Require Option.

Require Import Inequalities.
Require Export Notations.Sets.

(**
  Writes out an inequality chain as a big conjunction.
*)
Ltac2 simpl_ineq_chains () :=
  progress (repeat (
    (* TODO: do this in a more structured way *)
    match! goal with
      | [ h : total_statement _ |- _ ] => 
        cbn in $h
    end
  )).

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
  progress (repeat (
    match! goal with
      | [ h : (pred _ _) _ |- _ ] => simpl in $h
      | [ |- _ ] => ()
    end
  )).