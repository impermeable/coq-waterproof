(** * [sets_automation_tactics.v]
Authors: 
    - Cosmin Manea (1298542)

Creation date: 08 June 2021

Automation functions and tactic for statements regarding sets.
--------------------------------------------------------------------------------

This file is part of Waterproof-lib.

Waterproof-lib is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

Waterproof-lib is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with Waterproof-lib.  If not, see <https://www.gnu.org/licenses/>.
*)

From Ltac2 Require Import Ltac2.
From Ltac2 Require Import Message.
Require Import Reals.
Require Import Sets.Ensembles.
Require Import Sets.Classical_sets.
Require Import Waterproof.tactics.forward_reasoning.we_conclude_that.
Require Import Waterproof.set_intuition.Enabled.
Require Import Waterproof.set_search_depth.To_5.
Require Import Waterproof.load_database.Sets.

Hint Constructors Union Intersection Disjoint Full_set : sets.


(** * destruct_sets
    Destructs a statement regarding an element being contained in a union/intersection of two sets into
    its respective cases.

    Arguments:
        - no arguments.

    Does:
        - matches the goal with two possibilities: an element being contained in an intersection of sets
          or an element being contained in a union of sets.
        - in the first case, it just splits the goal into its respective subcases (i.e. the element
          being contained in every set in the intersecion).
        - in the second case, it just splits the goal into its respective subcases (i.e. the element
          being containined in one such set from the union), and then tries to solve the remaining of the proof.
*)
Ltac2 destruct_sets () :=
    lazy_match! goal with
        | [h : In _ (Intersection _ _ _) _ |- _ ] => let h_val := Control.hyp h in destruct $h_val
        | [h : In _ (Union _ _ _) _ |- _ ] => let h_val := Control.hyp h in
                                              destruct $h_val; try (solve_remainder_proof (Control.goal ()) None); 
                                              try (ltac1:(solve [firstorder (auto with sets)]));
                                              try (ltac1:(solve [firstorder (eauto with sets)]))
    end.



(** * trivial_set_inclusion
    Tries to prove a set inclusion.

    Arguments:
        - no arguments.

    Does:
        - calls the tactics/functions [intro], [intro], [destruct_sets], [contradiction] and various proof finishing functions,
          in this order, in order to automatically prove a set inclusion.
*)
Ltac2 trivial_set_inclusion () :=
    try (intro x); try (intro h); try (destruct_sets ()); ltac1:(try contradiction); try (solve_remainder_proof (Control.goal ()) None);
    try (ltac1:(solve [firstorder (auto with sets)])); try (ltac1:(solve [firstorder (eauto with sets)])).



(** * trivial_set_equality
    Prove a trivial set equality.

    Arguments:
        - no arguments.

    Does:
        - calls the tactics/functions [intros], [intros], [apply Extensionality_Ensembles],
          [unfold Same_set], [unfold Included], [split], and twice [trivial_set_inclusion],
          in order to prove a set equality.
*)
Ltac2 trivial_set_equality () :=
    try (intros A); try (intros B); try (apply Extensionality_Ensembles); try (unfold Same_set); 
    try (unfold Included); try (split); try (split); try (trivial); try (split);
    try (trivial_set_inclusion ()); try (trivial_set_inclusion ()).

Ltac2 Notation "This" "set" "equality" "is" "trivial" :=
    trivial_set_equality ().



(** Would like to add the following hint, but this undesirably interferes with workings of the other automation
    tactics. Also, what weight to use? *)
Hint Extern 5 (_ = _) => try (ltac2:(trivial_set_equality ())) : sets.



(** * we_prove_equality_by_proving_two_inclusions
      Prove a set equality of the form A = B by proving that A is a subset of B and B is a subset of A.

      Arguments:
          - No arguments.

      Does:
          - Proves that A = B by proving that A is a subset of B and B is a subset of A.
*)
Ltac2 we_prove_equality_by_proving_two_inclusions () :=
    try (ltac1:(apply Extensionality_Ensembles)); unfold Same_set; unfold Included; split.

Ltac2 Notation "We" "prove" "equality" "by" "proving" "two" "inclusions" :=
    we_prove_equality_by_proving_two_inclusions ().
