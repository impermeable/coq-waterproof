(** * Suprema and infima

Authors:
    - Jim Portegies

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

Require Import Reals.
Require Import Lra.
Require Import Classical.
Require Import Classical_Pred_Type.

Require Import Waterproof.selected_databases.
Require Import Waterproof.AllTactics.
Require Import Waterproof.contradiction_tactics.basic_contradiction.
Require Import Waterproof.load_database.All.
Require Import Waterproof.notations.notations.
Require Import Waterproof.definitions.set_definitions.
Require Import Waterproof.set_search_depth.To_5.
Require Import Waterproof.set_intuition.Disabled.
Require Import Waterproof.load_database.DisableWildcard.


Ltac2 Eval global_database_selection.

(** ## Upper bounds

A number $M : ℝ$ is called an **upper bound** of a subset $A : ℝ \to \mathsf{Prop}$ of the real numbers, if for all $a : ℝ$, if $a ∈ A$ then $a ≤ M$.*)
Definition is_upper_bound (A : subset_R) (M : ℝ) :=
  ∀ a : A, a ≤ M.
(** We say that a subset $A : ℝ \to \mathsf{Prop}$ is bounded above if there exists an $M : ℝ$ such that $M$ is an upper bound of $A$.
*)
Definition is_bounded_above (A : subset_R) :=
  ∃ M : ℝ, is_upper_bound A M.
(** ## The supremum

A real number $L : ℝ$ is called the **supremum** of a subset $A : ℝ \to \mathsf{Prop}$ if it is the smallest upper bound.
*)
Definition is_sup (A : subset_R) (L : ℝ) :=
  (is_upper_bound A L) ∧ (∀ M : ℝ, is_upper_bound A M ⇒ (L ≤ M) ).
(** 
We have to use `Waterproof.definitions.set_definitions` since `is_in`
  is doubly defined in [notations.v] as
  [Definition is_in {D : Set} := fun (A : (D → Prop)) 
   ↦ (fun (x : D) ↦ A x).]
*)
(* Notation is_in := Waterproof.definitions.set_definitions.is_in. *)

Lemma equivalence_upper_bounds :
  ∀ (A : subset_R) (L : ℝ),
    is_upper_bound A L ⇔
    Raxioms.is_upper_bound A L.
Proof.
    Take A : subset_R, L : ℝ.
    We show both directions.
    Assume L_upp_bd : (is_upper_bound A L).
    Expand the definition of Raxioms.is_upper_bound.
    That is, write the goal as (for all x : ℝ, A x ⇨ x ≤ L).
    Expand the definition of is_upper_bound in L_upp_bd.
    That is, write L_upp_bd as (for all a : A, a ≤ L).
    Take x : ℝ.
    Assume w : (A x).
    Define b := (mk_elem_R A x w).
    By L_upp_bd it holds that H : (b ≤ L).
    Apply H.

    Assume L_is_upp_bd : (Raxioms.is_upper_bound A L).
    Expand the definition of is_upper_bound.
    That is, write the goal as (for all a : A, a ≤ L).
    Expand the definition of Raxioms.is_upper_bound in L_is_upp_bd.
    That is, write L_is_upp_bd as (for all x : ℝ, A x ⇨ x ≤ L).
    Take a : A.
    Apply L_is_upp_bd.
    (** TODO subsets_elements_satisfy_predicate does not exist??? *)
    (* By subset_elements_satisfy_predicate it holds that h2: (is_in A a). *)
    (* By L_is_upp_bd it holds that (a ≤ L). *)

    
    This concludes the proof.
Qed.

Lemma equivalence_sup_lub :
  ∀ (A : subset_R) (M : ℝ),
  is_lub A M
  ⇔ is_sup A M.
Proof.
    Take A : subset_R, M : ℝ.
    We show both directions.

    - Assume M_is_sup_A : (is_lub A M).
      Expand the definition of is_lub, Raxioms.is_upper_bound in M_is_sup_A.
      That is, write M_is_sup_A as ((for all x : ℝ, A x ⇨ x ≤ M) 
        ∧ (for all b : ℝ, (for all x : ℝ, A x ⇨ x ≤ b) ⇨ M ≤ b)).
      Expand the definition of is_sup.
      That is, write the goal as 
        (is_upper_bound A M ∧ (for all M0 : ℝ, is_upper_bound A M0 ⇨ M ≤ M0)).
      We show both statements.
      + We need to show that ( is_upper_bound A M ).
        Expand the definition of is_upper_bound.
        That is, write the goal as (for all a : A, a ≤ M).
        Take a : A.
        destruct M_is_sup_A as [Mp1 Mp2].
        By Mp1 it holds that H : (a ≤ M).
        Apply H.
      + We need to show that (for all M0 : ℝ, is_upper_bound A M0 ⇨ M ≤ M0).
        Take M0 : ℝ.
        Assume M_is_ub_A : (is_upper_bound A M0).
        destruct M_is_sup_A as [M_is_R_ub_A M_is_R_lub_A].
        destruct (equivalence_upper_bounds A M0). 
        Apply (M_is_R_lub_A M0 (H M_is_ub_A)).

    - Assume M_is_sup_A : (is_sup A M).
      Expand the definition of is_lub.
      That is, write the goal as (Raxioms.is_upper_bound A M 
        ∧ (for all b : ℝ, Raxioms.is_upper_bound A b ⇨ M ≤ b)).
      Expand the definition of is_sup in M_is_sup_A.
      That is, write M_is_sup_A as (is_upper_bound A M 
        ∧ (for all M0 : ℝ, is_upper_bound A M0 ⇨ M ≤ M0)).
      We show both statements.
      + We need to show that (Raxioms.is_upper_bound A M).
        Expand the definition of Raxioms.is_upper_bound.
        That is, write the goal as (for all x : ℝ, A x ⇨ x ≤ M ).
        destruct M_is_sup_A. 
        Expand the definition of is_upper_bound in H.
        That is, write H as (for all a : A, a ≤ M).
        Take x : ℝ. 
        Assume x_in_A : (A x). 
        Define b := (mk_elem_R A x x_in_A).
        By H it holds that H1 : (b ≤ M).
        Apply H1.
      + We need to show that (for all b : ℝ, Raxioms.is_upper_bound A b ⇨ M ≤ b).
        Take b : ℝ.
        Assume M_is_R_lub_A : (Raxioms.is_upper_bound A b).
        destruct M_is_sup_A as [M_is_ub_A M_is_lub_A].
        Apply (M_is_lub_A b).
        destruct (equivalence_upper_bounds A b).
        Apply (H0 M_is_R_lub_A).
Qed.



(** ## The completeness axiom

The completeness axiom of the real numbers says that when a subset $A$ of the real numbers is bounded from above, and when there exists an element in the set, then there exists an $L$ such that $L$ is the supremum of $A$.*)
Lemma R_complete : ∀ (A : subset_R) (x : A),
  is_bounded_above A ⇒ sig (fun M : R => is_sup A M).
Proof.
    Take A : subset_R.
    Take a : A.
    Assume A_bdd_above : (is_bounded_above A).
    We claim that H : (sig (is_lub A)).
    Apply completeness.
    Expand the definition of is_bounded_above in A_bdd_above.
    That is, write A_bdd_above as (there exists M : ℝ, is_upper_bound A M).
    Expand the definition of is_upper_bound in A_bdd_above.
    That is, write A_bdd_above as (there exists M : ℝ, for all a0 : A, a0 ≤ M).
    Expand the definition of bound.
    That is, write the goal as (there exists m : ℝ, Raxioms.is_upper_bound A m).
    Choose M such that A_bdd_by_M according to A_bdd_above.
    Choose m := M.
    We need to show that (∀ a : ℝ, A a ⇒ a ≤ M).
    Take x : ℝ.
    Assume w : (A x).
    Define b := (mk_elem_R A x w).
    ltac1:(pose proof (A_bdd_by_M b)).
    This follows by assumption.
    Choose y := a.
    We use induction on y.
    This follows by assumption.
    Choose M such that M_upp_bd according to H.

    destruct (equivalence_sup_lub A M) as [M_is_sup_A H2]. 
    specialize (M_is_sup_A M_upp_bd).
    exists M. 
    exact M_is_sup_A.
Qed.



(** 
Axiom completeness : ∀ A : ℝ → Prop,
      is_bounded_above A ⇒ 
        ((∃ x : ℝ, x ∈ A) ⇒ { M : ℝ | is_sup A M }).
```*)
(** ## Lower bounds

A number $m : ℝ$ is called a lower bound of a subset $A : ℝ → \mathsf{Prop}$, if for all $a : \mathbb{R}$, if $a \in A$ then $a ≥ m$.*)
Definition is_lower_bound (A : subset_R) (m : ℝ) :=
  ∀ a : A, m ≤ a.
(** We say that a subset $A : ℝ → \mathsf{Prop}$ is bounded below if there exists an $m : ℝ$ such that $m$ is a lower bound of $A$.*)
Definition is_bounded_below (A : subset_R) :=
  ∃ m : ℝ, is_lower_bound A m.
(** ## The infimum

A real number $m : ℝ$ is called the **infimum** of a subset $A : ℝ → \mathsf{Prop}$ if it is the largest lower bound.*)
Definition is_inf :=
  fun (A : subset_R) m 
    => (is_lower_bound A m) ∧ (∀ l : R, is_lower_bound A l ⇒ l ≤ m).
(** ## Reflection of a subset of ℝ in the origin

Before we continue showing properties of the infimum, 
we first introduce the reflection of subsets of $\mathbb{R}$ 
in the origin. 
Given a subset $A : ℝ → \mathsf{Prop}$, 
we consider the set $-A$ 
(which we write as $\mathsf{set\_opp} A$), defined by*)
Definition set_opp (A : subset_R)  :=
  mk_subset_R (fun (x : ℝ) ↦ (A (-x))).


Definition original_elem {A : subset_R} : (set_opp A) -> A.
Proof.
    intro opp_a.
    (** TODO: this does not work for some reason *)
    (* It is not a forall goal. Also [intros] doesn't do anything here *)
    (* Take opp_a : (set_opp A). *)
    It holds that H1 : ((set_opp A) opp_a).
    It holds that H2 : (A (-opp_a)).
    exact (mk_elem_R A (-opp_a) H2).
Defined.


Lemma neg_opp_is_original_elem {A : subset_R} : 
  forall opp_a : (set_opp A), -opp_a = original_elem opp_a.
Proof.
    Take opp_a : (set_opp A).
    It holds that H : (-opp_a =  original_elem opp_a).
    Apply H.
Qed.


(** TODO: add this to additional lemmas.. *)
(** Hint Resolve neg_opp_is_original_elem : additional.*)
Lemma upp_bd_set_to_low_bd_set_opp :
  ∀ (A : subset_R) (M : ℝ),
    is_upper_bound A M ⇒ 
      is_lower_bound (set_opp A) (-M).
Proof.
    Take A : subset_R, M : ℝ.
    Assume M_upp_bd : (is_upper_bound A M).
    We need to show that (∀ a : (set_opp A),-M ≤ a).
    Expand the definition of is_lower_bound.
    That is, write the goal as (for all a : set_opp A, -M ≤ a).
    Take opp_a : (set_opp A).
    Define a := (original_elem opp_a).
    It holds that H1 : (A a).
    By M_upp_bd it holds that H2 : (a ≤ M).
    It holds that H3 : (-opp_a = a).
    It holds that H4 : (-M ≤ opp_a).
    Apply H4.
Qed.


Lemma low_bd_set_to_upp_bd_set_opp :
  ∀ (A : subset_R) (m : ℝ),
    is_lower_bound A m ⇒
      is_upper_bound (set_opp A) (-m).
Proof.
    Take A : subset_R, m : ℝ.
    Assume m_low_bd : (is_lower_bound A m).
    We need to show that (∀ opp_a : (set_opp A), opp_a ≤ -m).
    Expand the definition of is_upper_bound.
    That is, write the goal as (for all a : set_opp A, a ≤ -m).
    Take opp_a : (set_opp A).
    Define a := (original_elem opp_a).
    By m_low_bd it holds that H1 : (m ≤ a).
    It holds that H2 : (-opp_a = a).
    This concludes the proof.
Qed.


Lemma low_bd_set_opp_to_upp_bd_set :
  ∀ (A : subset_R) (m : ℝ),
    is_lower_bound (set_opp A) m ⇒ 
      is_upper_bound A (-m).
Proof.
    Take A : (subset_R), m : ℝ.
    Assume m_low_bd : (is_lower_bound (set_opp A) m).
    We need to show that (∀ a : A, a ≤ -m).
    Expand the definition of is_upper_bound.
    That is, write the goal as (for all a : A, a ≤ -m).
    Take a : A.
    Write m_low_bd as (∀ b : (set_opp A), m ≤ b).
    We claim that minmin_a_in_A : (A (--a)).
    Write goal using (--a = a) as (A a).
    It holds that H : (A a).
    This concludes the proof.
    It holds that min_a_in_set_opp_A : ((set_opp A) (-a)).
    (** By m_low_bd it holds that (m ≤ -a) (m_le_min_a).*)
    Define c := (mk_elem_R _ (-a) min_a_in_set_opp_A).
    We claim that m_le_c : (m ≤ c).
    Apply m_low_bd.
    It holds that m_le_min_a : (m ≤ -a).
    This concludes the proof.
Qed.


Lemma upp_bd_set_opp_to_low_bd_set :
  ∀ (A : subset_R) (M : ℝ),
    is_upper_bound (set_opp A) M ⇒
      is_lower_bound A (-M).
Proof.
    Take A : (subset_R), M : ℝ.
    Assume M_upp_bd : (is_upper_bound (set_opp A) M).
    We need to show that (∀ a : A, -M ≤ a).
    Expand the definition of is_lower_bound.
    That is, write the goal as (for all a : A, -M ≤ a).
    Take a : A.
    We claim that minmin_a_in_A : (A (--a)).
    Write goal using (--a = a) as (A a).
    This follows immediately.
    It holds that min_a_in_set_opp_A : ((set_opp A) (-a)).
    Define c := (mk_elem_R _ (-a) (min_a_in_set_opp_A)).
    By M_upp_bd it holds that mina_le_M : (c ≤ M).
    It holds that min_a_le_M : (-a ≤ M).
    This concludes the proof.
Qed.


Lemma bdd_below_to_bdd_above_set_opp :
  ∀ (A : subset_R),
    is_bounded_below A ⇒ is_bounded_above (set_opp A).
Proof.
    Take A : (subset_R). 
    Assume A_bdd_below : (is_bounded_below A).
    We need to show that (∃ M : ℝ, is_upper_bound (set_opp A) M).
    Expand the definition of is_bounded_above.
    That is, write the goal as (there exists M : ℝ, is_upper_bound (set_opp A) M).
    Write A_bdd_below as (∃ m : ℝ, is_lower_bound A m).
    Choose m such that m_low_bd according to A_bdd_below.
    
    Choose M := (-m).
    We need to show that (is_upper_bound (set_opp A) (-m)).
    Expand the definition of is_upper_bound.
    That is, write the goal as (for all a : set_opp A, a ≤ -m).
    By low_bd_set_to_upp_bd_set_opp it holds that H_con : (is_upper_bound (set_opp A) (-m)).
    This concludes the proof.
Qed.


Lemma sup_set_opp_is_inf_set :
  ∀ (A : subset_R) (M : ℝ),
    is_sup (set_opp A) M ⇒ is_inf A (-M).
Proof.
    Take A : (subset_R), M : ℝ.
    Assume M_is_sup : (is_sup (set_opp A) M).
    Expand the definition of is_inf.
    That is, write the goal as
      (is_lower_bound A (- M) ∧ (for all l : ℝ, is_lower_bound A l ⇨ l ≤ -M)).
    We show both statements.
    - We need to show that (is_lower_bound A (- M)).
      We claim that H0 : (is_upper_bound (set_opp A) M).
      Expand the definition of is_upper_bound.
      That is, write the goal as (for all a : set_opp A, a ≤ M).
      Take a : (set_opp A).
      Expand the definition of is_sup in M_is_sup.
      That is, write M_is_sup as (is_upper_bound (set_opp A) M 
        ∧ (for all M0 : ℝ, is_upper_bound (set_opp A) M0 ⇨ M ≤ M0)).
      destruct M_is_sup as [Mp1 Mp2].
      Expand the definition of is_upper_bound in Mp1.
      That is, write Mp1 as (for all a0 : set_opp A, a0 ≤ M).
      By Mp1 it holds that M_upp_bd : (is_upper_bound (set_opp A) M).
      This concludes the proof.

      By upp_bd_set_opp_to_low_bd_set it holds that H1 : (is_lower_bound A (-M)).
      Apply H1.

    - We need to show that (∀ l : ℝ, is_lower_bound A l ⇒ l ≤ -M).
      Take l : ℝ.
      Assume l_low_bd : (is_lower_bound A l).
      Expand the definition of is_sup in M_is_sup.
      That is, write M_is_sup as (is_upper_bound (set_opp A) M 
        ∧ (for all M0 : ℝ, is_upper_bound (set_opp A) M0 ⇨ M ≤ M0)).
      Because M_is_sup both Mp1 and Mp2.
      By Mp1 it holds that H1 : (∀ b : ℝ, is_upper_bound (set_opp A) b ⇒ M ≤ b).
      By low_bd_set_to_upp_bd_set_opp it holds that H2 : (is_upper_bound (set_opp A) (-l)).
      By H1 it holds that H3 : (M ≤ -l).
      This concludes the proof.
Qed.

Lemma exists_inf :
  ∀ (A : (subset_R)) (x : A), is_bounded_below A ⇒
    sig (fun (m : ℝ) ↦ is_inf A m).
Proof.
    Take A : (subset_R).
    Take z : A.
    Assume A_bdd_below : (is_bounded_below A).
    Define B := (set_opp A).
    We claim that B_bdd_above : (is_bounded_above B).
    Apply bdd_below_to_bdd_above_set_opp.
    Apply A_bdd_below.
    We claim that min_min_z_in_A : (A (--z)).
    Write goal using (--z = z) as (A z).
    This concludes the proof.

    It holds that min_z_in_B : ((set_opp A) (-z)).
    Define c := (mk_elem_R _ (-z) (min_z_in_B)).
    Define H := (R_complete B c B_bdd_above).
    Choose L such that L_is_sup_B according to H.
    By sup_set_opp_is_inf_set it holds that minL_is_inf_A : (is_inf A (-L)).
    exists (- L). (* TODO: remove this exists *)
    This concludes the proof.
Qed.

(** ### A supremum is an upper bound

If $M$ is the supremum of a set $A$, it is also an upper bound.*)
Lemma sup_is_upp_bd :
  ∀ A : (subset_R),
    ∀ M : ℝ,
      is_sup A M ⇒ is_upper_bound A M.
Proof.
    Take A : (subset_R).
    Take M : ℝ.
    Assume M_is_sup_A : (is_sup A M).
    Write M_is_sup_A as (is_upper_bound A M ∧ (∀ b: ℝ, is_upper_bound A b ⇒ M ≤ b) ).
    Because M_is_sup_A both A_upp_bd and every_upper_bound_smaller.
    It follows that (is_upper_bound A M).
Qed.

(** ### Any upper bound is greater than or equal to the supremum*)
Lemma any_upp_bd_ge_sup :
  ∀ A : (subset_R),
    ∀ M L : ℝ,
      is_sup A M ⇒ (is_upper_bound A L ⇒ M ≤ L).
Proof.
    Take A : (subset_R).
    Take M : ℝ.
    Take L : ℝ.
    (** TODO: fix this intro *)
    intro A_is_sup_M. 
(*    Assume A_is_sup_M : (is_supp A M). *)
    Assume L_is_upp_bd_A : (is_upper_bound A L).
    Because A_is_sup_M both M_is_upp_bd and any_upp_bd_le_M.
    (** We need to show that $M \leq L$.*)
    We conclude that (M ≤ L).
Qed.
(** ## Infima*)
(** ## An infimum is a lower bound*)
Lemma inf_is_low_bd :
  ∀ A : (subset_R),
    ∀ m : ℝ,
      is_inf A m ⇒ is_lower_bound A m.
Proof.
    Take A : (subset_R).
    Take m : R.
    Assume m_is_inf_A : (is_inf A m).
    Because m_is_inf_A both m_is_low_bd and any_low_bd_ge_m.
    By m_is_low_bd we conclude that (is_lower_bound A m).
Qed.
(** ## Any lower bound is less than or equal to the infimum*)
Lemma any_low_bd_le_inf :
  ∀ A : (subset_R),
    ∀ m l : ℝ,
      is_inf A m ⇒ is_lower_bound A l ⇒ l ≤ m.
Proof.
    Take A : (subset_R).
    Take m : ℝ.
    Take l : ℝ.
    (** TODO: fix this intro *)
    intro m_is_inf_A.
    (* Assume m_is_inf_A : (is_inf A m). *)
    Assume l_is_low_bd_A : (is_lower_bound A l).
    Because m_is_inf_A both m_low_bd and any_low_bd_le_m.
    We conclude that (l ≤m).
Qed.

(** ### $\varepsilon$-characterizations*)
Lemma exists_almost_maximizer :
  ∀ (A : subset_R) (M : ℝ),
    is_sup A M ⇒
      ∀ (L : ℝ), L < M ⇒ 
        ∃ a : A, L < a.
Proof.
    Take A : (subset_R).
    Take M : ℝ.
    Assume M_is_sup_A : (is_sup A M).
    Take L : ℝ.
    Assume L_lt_M : (L < M).
    We argue by contradiction.
    We claim that H0 : (∀ x : A, ¬ (L < x)).
    Apply not_ex_all_not.
    Apply H.
    We claim that H1 : (∀ x : A, x ≤ L).
    Take x : A.
    It holds that H2 : (¬(L < x)).
    We need to show that (x ≤ L).
    We conclude that (x ≤ L).
    By H1 it holds that H3 : (is_upper_bound A L).
    (** TODO: why can't this be done automatically? *)
    We claim that H4 : (M ≤ L).
    Apply (any_upp_bd_ge_sup A).
    Apply M_is_sup_A.
    Apply H3.
    It holds that H5 : (¬(M ≤ L)).
    Contradiction.
Qed.

Lemma exists_almost_minimizer :
  ∀ (A : subset_R) (m : ℝ),
    is_inf A m ⇒
      ∀ (L : ℝ), L > m ⇒ 
        ∃ a : A, L > a.
Proof.
    Take A : (subset_R).
    Take m : ℝ.
    Assume M_is_inf_A : (is_inf A m).
    Take L : ℝ.
    Assume L_gt_m : (L > m).
    We argue by contradiction.
    We claim that H0 : (∀ x : A, ¬ (L > x)).
    Apply not_ex_all_not.
    Apply H.
    We claim that H1 : (∀ x : A, L ≤ x).
    Take x : A.
    It holds that H2 : (¬(L > x)).
    We need to show that (L ≤ x).
    We conclude that (L ≤ x).
    By H1 it holds that H3 : (is_lower_bound A L).
    (** TODO: why can't this be done automatically? *)
    We claim that H4 : (L ≤ m).
    Apply (any_low_bd_le_inf A).
    Apply M_is_inf_A.
    Apply H3.
    It holds that H5 : (¬(L ≤ m)).
    Contradiction.
Qed.

Lemma if_almost_maximizer_then_every_upp_bd_larger :
  ∀ (A : subset_R) (M : ℝ),
    (∀ (L : ℝ), L < M ⇒ ∃ a : A, L < a)
       ⇒ ∀ (K : ℝ), is_upper_bound A K ⇒ M ≤ K.
Proof.
Take A : subset_R, M : ℝ.
Assume exists_almost_max :
  (∀ L : ℝ, L < M ⇒ there exists a : A ,
             L < a).
Take K : ℝ.
Assume K_upper_bound : (is_upper_bound A K).
Expand the definition of is_upper_bound in K_upper_bound.
That is, write K_upper_bound as
  (∀ a : A, a ≤ K).
We need to show that (M ≤ K).
We argue by contradiction.
It holds that M_gt_K : (M > K).
By exists_almost_max it holds that exists_a :
  (∃ a : A, K < a).
Choose a such that K_lt_a according to exists_a.
By K_upper_bound it holds that a_le_K : (a ≤ K).
It holds that K_lt_K : (K < K).
It holds that not_K_lt_K : (¬ (K < K)).
Contradiction.
Qed.

Lemma if_almost_minimizer_then_every_low_bd_smaller :
  ∀ (A : subset_R) (m : ℝ),
    (∀ (L : ℝ), L > m ⇒ ∃ a : A, L > a)
       ⇒ ∀ (K : ℝ), is_lower_bound A K ⇒ K ≤ m.
Proof.
Take A : subset_R, m : ℝ.
Assume exists_almost_min :
  (∀ L : ℝ, L > m ⇒ there exists a : A ,
             L > a).
Take K : ℝ.
Assume K_lower_bound : (is_lower_bound A K).
Expand the definition of is_lower_bound in K_lower_bound.
That is, write K_lower_bound as
  (∀ a : A, K ≤ a).
We need to show that (K ≤ m).
We argue by contradiction.
It holds that K_gt_m : (K > m).
By exists_almost_min it holds that exists_a :
  (∃ a : A, K > a).
Choose a such that K_gt_a according to exists_a.
By K_lower_bound it holds that K_le_a : (K ≤ a).
It holds that K_gt_K : (K > K).
It holds that not_K_lt_K : (¬ (K > K)).
Contradiction.
Qed.

Lemma if_almost_maximizer_ε_then_every_upp_bd_larger :
  ∀ (A : subset_R) (M : ℝ),
    (∀ (ε : ℝ), ε > 0 ⇒ ∃ a : A, M - ε < a)
       ⇒ ∀ (K : ℝ), is_upper_bound A K ⇒ M ≤ K.
Proof.
Take A : subset_R, M : ℝ.
Assume exists_almost_max_ε : (for all ε : ℝ,
   ε > 0 ⇨ there exists a : A ,
             M - ε < a).
Apply if_almost_maximizer_then_every_upp_bd_larger.
Take L : ℝ.
Assume L_lt_M : (L < M).
It holds that M_min_L_pos : (M - L > 0).
Define ε1 := (M - L).
It holds that ε1_pos : (ε1 > 0).
By exists_almost_max_ε it holds that exists_a :
  (there exists a : A , M - ε1 < a).
Choose a0 such that a_gt_M_min_ε1 according to exists_a.
Choose a := a0.
(** TODO: due to something with coercions we cannot immediately 
rewrite the whole inequality *)
Rewrite inequality L "=" (M - (M - L)) "=" (M - ε1).
We conclude that (M -ε1 < a0).
Qed.

Lemma if_almost_minimizer_ε_then_every_low_bd_smaller :
  ∀ (A : subset_R) (m : ℝ),
    (∀ (ε : ℝ), ε > 0 ⇒ ∃ a : A, m + ε > a)
       ⇒ ∀ (K : ℝ), is_lower_bound A K ⇒ K ≤ m.
Proof.
Take A : subset_R, m : ℝ.
Assume exists_almost_min_ε : (for all ε : ℝ,
   ε > 0 ⇨ there exists a : A ,
             m + ε > a).
Apply if_almost_minimizer_then_every_low_bd_smaller.
Take L : ℝ.
Assume L_gt_m : (L > m).
It holds that L_min_m_pos : (L - m > 0).
Define ε1 := (L - m).
It holds that ε1_pos : (ε1 > 0).
By exists_almost_min_ε it holds that exists_a :
  (there exists a : A , m + ε1 > a).
Choose a0 such that a_lt_m_plus_ε1 according to exists_a.
Choose a := a0.
(** TODO: due to something with coercions we cannot immediately 
rewrite the whole inequality *)
Rewrite inequality L "=" (m + (L-m)) "=" (m + ε1).
We conclude that (m + ε1 > a).
Qed.

Lemma exists_almost_maximizer_ε :
  ∀ (A : subset_R) (M : ℝ),
    is_sup A M ⇒
      ∀ (ε : ℝ), ε > 0 ⇒ 
        ∃ a : A, M - ε < a.
Proof.
    Take A : (subset_R).
    Take M : ℝ.
    Assume M_is_sup_A : (is_sup A M).
    Take ε : ℝ.
    Assume ε_gt_0 : (ε > 0).
    It holds that H1 : (M - ε < M). 
    (** TODO: fix this *)
    apply exists_almost_maximizer with (L := M- ε) (M := M); assumption.
Qed.

Lemma exists_almost_minimizer_ε :
  ∀ (A : subset_R) (m : ℝ),
    is_inf A m ⇒
      ∀ (ε : ℝ), ε > 0 ⇒ 
        ∃ a : A, m + ε > a.
Proof.
    Take A : (subset_R).
    Take m : ℝ.
    Assume m_is_inf_A : (is_inf A m).
    Take ε : ℝ.
    Assume ε_gt_0 : (ε > 0).
    It holds that H1 : (m + ε > m). 
    (** TODO: fix this *)
    apply exists_almost_minimizer with (L := m + ε) (m := m); assumption.
Qed.

Definition is_sup_alt_char (A : subset_R) (M : ℝ):=
  is_upper_bound A M ∧ (∀ (ε : ℝ), ε > 0 ⇒ 
        ∃ a : A, M - ε < a).

Definition is_inf_alt_char (A : subset_R) (m : ℝ):=
  is_lower_bound A m ∧ (∀ (ε : ℝ), ε > 0 ⇒ 
        ∃ a : A, m + ε > a).

Theorem alt_char_sup :
  ∀ (A : subset_R) (M : ℝ),
    is_sup A M ⇔ is_sup_alt_char A M.
Proof.
Take A : subset_R, M : ℝ.
We show both directions.
- Assume M_is_sup_A : (is_sup A M).
  Expand the definition of is_sup_alt_char.
  That is, write the goal as (
  is_upper_bound A M
  ∧ (for all ε : ℝ,
     ε > 0 ⇨ there exists a : A ,
               M - ε < a) ).
  We show both statements.
  + We need to show that (is_upper_bound A M).
    Expand the definition of is_sup in M_is_sup_A.
    That is, write M_is_sup_A as (
    is_upper_bound A M
     ∧ (for all M0 : ℝ,
      is_upper_bound A M0 ⇨ M ≤ M0) ).
    Because M_is_sup_A both M_is_upp_bd and every_upp_bd_ge_M.
    It follows that (is_upper_bound A M).

  + We need to show that (for all ε : ℝ, ε > 0 ⇨ there exists a : A, M - ε < a ).
    By exists_almost_maximizer_ε we conclude that
   (  for all ε : ℝ,
      ε > 0 ⇨ there exists a : A ,
            M - ε < a).

- Assume M_alt_sup : (is_sup_alt_char A M).
  Expand the definition of is_sup_alt_char in M_alt_sup.
  That is, write M_alt_sup as (
  is_upper_bound A M
   ∧ (for all ε : ℝ,
     ε > 0 ⇨ there exists a : A ,
               M - ε < a) ).
  Because M_alt_sup both M_upp_bd and eps_char.

  Expand the definition of is_sup.
  That is, write the goal as (
  is_upper_bound A M
  ∧ (for all M0 : ℝ,
     is_upper_bound A M0 ⇨ M ≤ M0) ).
  We show both statements.
  + We need to show that (is_upper_bound A M).
    By M_upp_bd we conclude that (is_upper_bound A M).
  + We need to show that (for all M0 : ℝ, is_upper_bound A M0 ⇨ M ≤ M0).
    By if_almost_maximizer_ε_then_every_upp_bd_larger
    we conclude that (for all M0 : ℝ,
    is_upper_bound A M0 ⇨ M ≤ M0).
Qed.

Theorem alt_char_inf :
  ∀ (A : subset_R) (m : ℝ),
    is_inf A m ⇔ is_inf_alt_char A m.
Proof.
Take A : subset_R, m : ℝ.
We show both directions.
- Assume m_is_inf_A : (is_inf A m).
  Expand the definition of is_inf_alt_char.
  That is, write the goal as (
  is_lower_bound A m
  ∧ (for all ε : ℝ,
     ε > 0 ⇨ there exists a : A ,
               m + ε > a) ).
  We show both statements.
  + We need to show that (is_lower_bound A m).
    Expand the definition of is_inf in m_is_inf_A.
    That is, write m_is_inf_A as (
    is_lower_bound A m ∧ (for all l : ℝ,
                        is_lower_bound A l ⇨ l ≤ m) 
    ).
    Because m_is_inf_A both m_is_low_bd and every_low_bd_le_m.
    It follows that (is_lower_bound A m).

  + We need to show that (for all ε : ℝ, ε > 0 
      ⇨ there exists a : A, m + ε > a).
    By exists_almost_minimizer_ε we conclude that
    (for all ε : ℝ,
       ε > 0 ⇨ there exists a : A ,
            m + ε > a).

- Assume m_alt_inf : (is_inf_alt_char A m).
  Expand the definition of is_inf_alt_char in m_alt_inf.
  That is, write m_alt_inf as (
    is_lower_bound A m
     ∧ (for all ε : ℝ,
     ε > 0 ⇨ there exists a : A ,
               m + ε > a) ).
  Because m_alt_inf both m_low_bd and eps_char.

  Expand the definition of is_inf.
  That is, write the goal as (
    is_lower_bound A m ∧ (for all l : ℝ,
                        is_lower_bound A l ⇨ l ≤ m)
   ).
  We show both statements.
  + We need to show that (is_lower_bound A m).
    By m_low_bd we conclude that (is_lower_bound A m).
  + We need to show that (for all l : ℝ, is_lower_bound A l ⇨ l ≤ m).
    By if_almost_minimizer_ε_then_every_low_bd_smaller
    we conclude that (for all l : ℝ,
    is_lower_bound A l ⇨ l ≤ m).
Qed.


Lemma max_or_strict :
  ∀ (A : subset_R) (M : ℝ),
    is_sup A M ⇒ 
      (A M) ∨ (∀ a : A, a < M).
Proof.
    Take A : (subset_R).
    Take M : ℝ.
    Assume M_is_sup_A : (is_sup A M).
    We argue by contradiction. 
    By not_or_and it holds that H1 : ((¬ (A M)) ∧ 
      ¬(∀ a : A, a < M) ).
    Because H1 both H2 and H3.
    (** TODO: fix *)
    (** We only show the proposition on the *)
    right
    (** hand side of the or-sign, i.e. we will show that for all $a \in \mathbb{R}$, if $a \in A$ then $a < M$*)
    .
    Take a : A.
    By sup_is_upp_bd it holds that M_upp_bd : (is_upper_bound A M).
    It holds that a_le_M : (a ≤ M).
    We claim that M_is_not_a : (M ≠ a).
    We argue by contradiction.
    We claim that H4 : ((M = a) ⇒ False).
    Assume M_eq_a : (M = a).
    We claim that M_in_A : (A M).
    Rewrite using (M = a).
    We conclude that (A a).
    Contradiction.
    We conclude that (M ≠ a).
    We conclude that (a < M).
Qed.
(** * Lemmas for convenience*)
Lemma bounded_by_upper_bound_propform :
  ∀ (A : subset_R) (M : ℝ) (b : ℝ),
    is_upper_bound A M ⇒ A b ⇒ b ≤ M.
Proof.
    Take A : subset_R.
    Take M : ℝ.
    Take b : ℝ.
    (** TODO: fix 
    Assume M_upp_bd : (is_upper_bound A M). *)
    intro M_upp_bd.
    Assume b_in_A : (A b).
    Define c := (mk_elem_R A b b_in_A).
    Expand the definition of is_upper_bound in M_upp_bd.
    That is, write M_upp_bd as (for all a : A, a ≤ M).
    By M_upp_bd it holds that c_le_M : (c ≤ M).
    We conclude that (b ≤ M).
Qed.

Lemma bounded_by_lower_bound_propform :
  ∀ (A : subset_R) (m : ℝ) (b : ℝ),
    is_lower_bound A m ⇒ A b ⇒ m ≤ b.
Proof.
    Take A : subset_R.
    Take m : ℝ.
    Take b: ℝ.
    (** TODO: fix 
    Assume m_low_bd : (is_lower_bound A m). *)
    intro m_low_bd.
    Assume b_in_A : (A b).
    Define c := (mk_elem_R A b b_in_A).
    Expand the definition of is_lower_bound in m_low_bd.
    That is, write m_low_bd as (for all a : A, m ≤ a).
    By m_low_bd it holds that m_le_c : (m ≤ c).
    We conclude that (m ≤ b).
Qed.

Global Hint Resolve bounded_by_upper_bound_propform : additional.
Global Hint Resolve bounded_by_lower_bound_propform : additional.
Global Hint Resolve alt_char_inf : additional.
Global Hint Resolve alt_char_sup : additional.
(** ### **Hints***)
Hint Extern 1 => (unfold is_sup) : unfolds.
Hint Extern 1 => (unfold is_inf) : unfolds.
