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
Require Import Waterproof.load_database.Subsets.
Require Import Waterproof.load_database.RealsAndIntegers.
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
    Take A : subset_R and L : ℝ.
    We show both directions.
    - We need to show that (is_upper_bound A L ⇨ Raxioms.is_upper_bound A L).
      Assume that (is_upper_bound A L) (i).
      Expand the definition of Raxioms.is_upper_bound.
      That is, write the goal as (for all x : ℝ, A x ⇨ x ≤ L).
      Expand the definition of is_upper_bound in (i).
      That is, write (i) as (for all a : A, a ≤ L).
      Take x : ℝ.
      Assume that (A x) (ii).
      Define b := (mk_elem_R A x (ii)).
      By (ii) it holds that (b ≤ L).
      We conclude that (x <= L).
    - We need to show that ( Raxioms.is_upper_bound A L ⇨ is_upper_bound A L).
      Assume that (Raxioms.is_upper_bound A L) (i).
      Expand the definition of is_upper_bound.
      That is, write the goal as (for all a : A, a ≤ L).
      Expand the definition of Raxioms.is_upper_bound in (i).
      That is, write (i) as (for all x : ℝ, A x ⇨ x ≤ L).
      Take a : A.
      We conclude that (a <= L).
Qed.

Lemma equivalence_sup_lub :
  ∀ (A : subset_R) (M : ℝ),
  is_lub A M
  ⇔ is_sup A M.
Proof.
    Take A : subset_R and M : ℝ.
    We show both directions.
    - We need to show that (is_lub A M ⇨ is_sup A M).
      Assume that (is_lub A M) (i).
      Expand the definition of is_lub, Raxioms.is_upper_bound in (i).
      That is, write (i) as ((for all x : ℝ, A x ⇨ x ≤ M)
        ∧ (for all b : ℝ, (for all x : ℝ, A x ⇨ x ≤ b) ⇨ M ≤ b)).
      Because (i) both (for all x : ℝ, A x ⇨ x ≤ M) (ii) and
          (for all b : ℝ, (for all x : ℝ, A x ⇨ x ≤ b) ⇨ M ≤ b) hold.
      Expand the definition of is_sup.
      That is, write the goal as 
        (is_upper_bound A M ∧ (for all M0 : ℝ, is_upper_bound A M0 ⇨ M ≤ M0)).
      We show both statements.
      + We need to show that ( is_upper_bound A M ).
        Expand the definition of is_upper_bound.
        That is, write the goal as (for all a : A, a ≤ M).
        Take a : A.
        By (ii) we conclude that (a ≤ M).
      + We need to show that (for all M0 : ℝ, is_upper_bound A M0 ⇨ M ≤ M0).
        Take M0 : ℝ.
        Assume that (is_upper_bound A M0).
        By equivalence_upper_bounds it holds that
          (is_upper_bound A M0 ⇔ Raxioms.is_upper_bound A M0) (iii).
        Because (iii) both (is_upper_bound A M0 -> Raxioms.is_upper_bound A M0)
          and (Raxioms.is_upper_bound A M0 -> is_upper_bound A M0) hold.
        It holds that (Raxioms.is_upper_bound A M0).
        We conclude that (M <= M0).
    - We need to show that (is_sup A M ⇨ is_lub A M).
      Assume that (is_sup A M) (i).
      Expand the definition of is_lub.
      That is, write the goal as (Raxioms.is_upper_bound A M 
        ∧ (for all b : ℝ, Raxioms.is_upper_bound A b ⇨ M ≤ b)).
      Expand the definition of is_sup in (i).
      That is, write (i) as (is_upper_bound A M 
        ∧ (for all M0 : ℝ, is_upper_bound A M0 ⇨ M ≤ M0)).
      Because (i) both (is_upper_bound A M) (ii) and
        (for all M0 : ℝ, is_upper_bound A M0 ⇨ M ≤ M0) hold.
      We show both statements.
      + We need to show that (Raxioms.is_upper_bound A M).
        Expand the definition of Raxioms.is_upper_bound.
        That is, write the goal as (for all x : ℝ, A x ⇨ x ≤ M).
        Expand the definition of is_upper_bound in (ii).
        That is, write (ii) as (for all a : A, a ≤ M).
        Take x : ℝ.
        Assume that (A x) (iii).
        Define b := (mk_elem_R A x (iii)).
        By (ii) we conclude that (b ≤ M).
      + We need to show that (for all b : ℝ, Raxioms.is_upper_bound A b ⇨ M ≤ b).
        Take b : ℝ.
        Assume that (Raxioms.is_upper_bound A b).
        It suffices to show that (is_upper_bound A b).
        By equivalence_upper_bounds it holds that
          (is_upper_bound A b ⇔ Raxioms.is_upper_bound A b) (iv).
        Because (iv) both (is_upper_bound A b -> Raxioms.is_upper_bound A b)
          and (Raxioms.is_upper_bound A b -> is_upper_bound A b) hold.
        We conclude that (is_upper_bound A b).
Qed.



(** ## The completeness axiom

The completeness axiom of the real numbers says that when a subset $A$ of the real numbers is bounded from above, and when there exists an element in the set, then there exists an $L$ such that $L$ is the supremum of $A$.*)
Lemma R_complete : ∀ (A : subset_R) (x : A),
  is_bounded_above A ⇒ exists M : R, is_sup A M.
Proof.
    Take A : subset_R.
    Take a : A.
    Assume that (is_bounded_above A) (i).
    We claim that (bound A).
    { Expand the definition of bound.
      That is, write the goal as (there exists m : ℝ, Raxioms.is_upper_bound A m).
      Expand the definition of is_bounded_above in (i).
      That is, write (i) as (there exists M : R, is_upper_bound A M).
      Obtain M according to (i), so for M : R it holds that (is_upper_bound A M).
      Choose m := M.
      We need to show that (∀ a : ℝ, A a ⇒ a ≤ M).
      Take x : R.
      Assume that (A x) (ii).
      Define b := (mk_elem_R A x (ii)).
      It holds that (b ≤ M).
      We conclude that (x <= M).
    }
    We claim that (there exists x : ℝ, A x).
    { Choose (a).
      We conclude that (A a).
    }
    By completeness it holds that (sig (is_lub A)) (ii).
    Obtain M according to (ii), so for M : R it holds that (is_lub A M).
    By equivalence_sup_lub it holds that
      (is_lub A M ⇔ is_sup A M) (iii).
    Because (iii) both (is_lub A M -> is_sup A M) and
      (is_sup A M -> is_lub A M) hold.
    Choose M0 := M.
    We need to show that (is_sup A M).
    We conclude that (is_sup A M).
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
    It holds that ((set_opp A) opp_a).
    It holds that (A (-opp_a)) (i).
    exact (mk_elem_R A (-opp_a) (i)).
Defined.


Lemma neg_opp_is_original_elem {A : subset_R} : 
  forall opp_a : (set_opp A), -opp_a = original_elem opp_a.
Proof.
    Take opp_a : (set_opp A).
    We conclude that (-opp_a =  original_elem opp_a).
Qed.


(** TODO: add this to additional lemmas.. *)
(** Hint Resolve neg_opp_is_original_elem : additional.*)
Lemma upp_bd_set_to_low_bd_set_opp :
  ∀ (A : subset_R) (M : ℝ),
    is_upper_bound A M ⇒ 
      is_lower_bound (set_opp A) (-M).
Proof.
    Take A : subset_R and M : ℝ.
    Assume that (is_upper_bound A M) (i).
    We need to show that (∀ a : (set_opp A),-M ≤ a).
    Expand the definition of is_lower_bound.
    That is, write the goal as (for all a : set_opp A, -M ≤ a).
    Take opp_a : (set_opp A).
    Define a := (original_elem opp_a).
    It holds that (A a).
    By (i) it holds that (a ≤ M).
    It holds that (-opp_a = a).
    We conclude that (-M ≤ opp_a).
Qed.


Lemma low_bd_set_to_upp_bd_set_opp :
  ∀ (A : subset_R) (m : ℝ),
    is_lower_bound A m ⇒
      is_upper_bound (set_opp A) (-m).
Proof.
    Take A : subset_R and m : ℝ.
    Assume that (is_lower_bound A m) (i).
    We need to show that (∀ opp_a : (set_opp A), opp_a ≤ -m).
    Expand the definition of is_upper_bound.
    That is, write the goal as (for all a : set_opp A, a ≤ -m).
    Take opp_a : (set_opp A).
    Define a := (original_elem opp_a).
    By (i) it holds that (m ≤ a).
    We conclude that (& opp_a &= -a &<= -m).
Qed.


Lemma low_bd_set_opp_to_upp_bd_set :
  ∀ (A : subset_R) (m : ℝ),
    is_lower_bound (set_opp A) m ⇒ 
      is_upper_bound A (-m).
Proof.
    Take A : (subset_R) and m : ℝ.
    Assume that (is_lower_bound (set_opp A) m) (i).
    We need to show that (∀ a : A, a ≤ -m).
    Expand the definition of is_upper_bound.
    That is, write the goal as (for all a : A, a ≤ -m).
    Take a : A.
    Expand the definition of is_lower_bound in (i).
    That is, write (i) as (for all b : set_opp A, m ≤ b).
    We claim that (A (--a)).
    { It holds that (--a = a) (ii).
      It holds that (A a) (iii).
      (* TODO: We conclude that (--a ∈ A). should work *)
      exact (eq_ind_r (fun x => A x) (iii) (ii)).
    }
    It holds that ((set_opp A) (-a)) (ii).
    (** By m_low_bd it holds that (m ≤ -a) (m_le_min_a).*)
    Define c := (mk_elem_R _ (-a) (ii)).
    It holds that (m ≤ c).
    It holds that (m ≤ -a).
    We conclude that (a ≤ - m).
Qed.


Lemma upp_bd_set_opp_to_low_bd_set :
  ∀ (A : subset_R) (M : ℝ),
    is_upper_bound (set_opp A) M ⇒
      is_lower_bound A (-M).
Proof.
    Take A : (subset_R) and M : ℝ.
    Assume that (is_upper_bound (set_opp A) M) (i).
    We need to show that (∀ a : A, -M ≤ a).
    Expand the definition of is_lower_bound.
    That is, write the goal as (for all a : A, -M ≤ a).
    Take a : A.
    We claim that (A (--a)).
    { It holds that (--a = a) (ii).
      It holds that (A a) (iii).
      (* TODO: We conclude that (--a ∈ A). should work *)
      exact (eq_ind_r (fun x => A x) (iii) (ii)).
    }
    It holds that ((set_opp A) (-a)) (iv).
    Define c := (mk_elem_R _ (-a) (iv)).
    By (i) it holds that (c ≤ M).
    It holds that (-a ≤ M).
    We conclude that (- M ≤ a).
Qed.


Lemma bdd_below_to_bdd_above_set_opp :
  ∀ (A : subset_R),
    is_bounded_below A ⇒ is_bounded_above (set_opp A).
Proof.
    Take A : (subset_R).
    Assume that (is_bounded_below A) (i).
    We need to show that (∃ M : ℝ, is_upper_bound (set_opp A) M).
    Expand the definition of is_bounded_above.
    That is, write the goal as (there exists M : ℝ, is_upper_bound (set_opp A) M).
    Expand the definition of is_bounded_below in (i).
    That is, write (i) as (there exists m : ℝ, is_lower_bound A m).
    Obtain m according to (i), so for m : R it holds that (is_lower_bound A m).
    
    Choose M := (-m).
    By low_bd_set_to_upp_bd_set_opp we conclude that (is_upper_bound (set_opp A) (-m)).
Qed.


Lemma sup_set_opp_is_inf_set :
  ∀ (A : subset_R) (M : ℝ),
    is_sup (set_opp A) M ⇒ is_inf A (-M).
Proof.
    Take A : (subset_R) and M : ℝ.
    Assume that (is_sup (set_opp A) M) (i).
    Expand the definition of is_sup in (i).
      That is, write (i) as (is_upper_bound (set_opp A) M 
        ∧ (for all M0 : ℝ, is_upper_bound (set_opp A) M0 ⇨ M ≤ M0)).
      Because (i) both (is_upper_bound (set_opp A) M) (ii) and
        (for all M0 : ℝ, is_upper_bound (set_opp A) M0 ⇨ M ≤ M0) hold.
    Expand the definition of is_inf.
    That is, write the goal as
      (is_lower_bound A (- M) ∧ (for all l : ℝ, is_lower_bound A l ⇨ l ≤ -M)).
    We show both statements.
    - We need to show that (is_lower_bound A (- M)).
      We claim that (is_upper_bound (set_opp A) M).
      Expand the definition of is_upper_bound.
      That is, write the goal as (for all a : set_opp A, a ≤ M).
      Take a : (set_opp A).
      
      Expand the definition of is_upper_bound in (ii).
      That is, write (ii) as (for all a0 : set_opp A, a0 ≤ M).
      By (ii) it holds that (is_upper_bound (set_opp A) M).
      We conclude that (a <= M).

      By upp_bd_set_opp_to_low_bd_set we conclude that (is_lower_bound A (-M)).

    - We need to show that (∀ l : ℝ, is_lower_bound A l ⇒ l ≤ -M).
      Take l : ℝ.
      Assume that (is_lower_bound A l).
      Expand the definition of is_sup in (i).
      That is, write (i) as (is_upper_bound (set_opp A) M 
        ∧ (for all M0 : ℝ, is_upper_bound (set_opp A) M0 ⇨ M ≤ M0)).
      By (ii) it holds that (∀ b : ℝ, is_upper_bound (set_opp A) b ⇒ M ≤ b) (iii).
      By low_bd_set_to_upp_bd_set_opp it holds that (is_upper_bound (set_opp A) (-l)).
      By (iii) it holds that (M ≤ -l).
      We conclude that (l ≤ - M).
Qed.

Lemma exists_inf :
  ∀ (A : (subset_R)) (x : A), is_bounded_below A ⇒
    exists (m : ℝ), is_inf A m.
Proof.
    Take A : (subset_R).
    Take z : A.
    Assume that (is_bounded_below A).
    Define B := (set_opp A).
    We claim that (is_bounded_above B) (i).
    { By bdd_below_to_bdd_above_set_opp it suffices to show that (is_bounded_below A).
      We conclude that (is_bounded_below A).
    }
    We claim that (A (--z)).
    { It holds that (--z = z) (ii).
      It holds that (A z) (iii).
      (* TODO: We conclude that (--z ∈ A). should work *)
      exact (eq_ind_r (fun x => A x) (iii) (ii)).
    }
    It holds that ((set_opp A) (-z)) (iv).
    Define c := (mk_elem_R _ (-z) (iv)).
    By R_complete it holds that (there exists M : ℝ, is_sup B M) (v).
    Obtain M according to (v), so for M : R it holds that (is_sup B M).
    Choose m := (- M).
    By sup_set_opp_is_inf_set we conclude that (is_inf A m).
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
    Assume that (is_sup A M) (i).
    Expand the definition of is_sup in (i).
    That is, write (i) as (is_upper_bound A M 
      ∧ (for all b : ℝ, is_upper_bound A b ⇨ M ≤ b)).
    Because (i) both (is_upper_bound A M) and
      (for all M0 : ℝ, is_upper_bound A M0 ⇨ M ≤ M0) hold.
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
    Assume that (is_sup A M) (i).
    Assume that (is_upper_bound A L).
    Because (i) both (is_upper_bound A M) and
      (for all M0 : ℝ, is_upper_bound A M0 ⇨ M ≤ M0) hold.
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
    Assume that (is_inf A m) (i).
    Because (i) both (is_lower_bound A m) (ii) and
      (for all M0 : ℝ, is_lower_bound A M0 ⇨ M0 ≤ m) hold.
    By (ii) we conclude that (is_lower_bound A m).
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
    Assume that (is_inf A m) (i).
    Assume that (is_lower_bound A l).
    Because (i) both (is_lower_bound A m) and
      (for all M0 : ℝ, is_lower_bound A M0 ⇨ M0 ≤ m) hold.
    We conclude that (l ≤ m).
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
    Assume that (is_sup A M).
    Take L : ℝ.
    Assume that (L < M).
    We argue by contradiction.
    Assume that (¬ (there exists a : A, L < a)).
    It holds that (∀ x : A, x <= L) (i).
    By (i) it holds that (is_upper_bound A L).
    (** TODO: why can't this be done automatically? *)
    By any_upp_bd_ge_sup it holds that (M <= L).
    It holds that (¬(M ≤ L)).
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
    Assume that (is_inf A m).
    Take L : ℝ.
    Assume that (L > m).
    We argue by contradiction.
    Assume that (¬ (there exists a : A, L > a)).
    It holds that (∀ x : A, L ≤ x) (i).
    By (i) it holds that (is_lower_bound A L).
    (** TODO: why can't this be done automatically? *)
    By any_low_bd_le_inf it holds that (L <= m).
    It holds that (¬(L ≤ m)).
    Contradiction.
Qed.

Lemma if_almost_maximizer_then_every_upp_bd_larger :
  ∀ (A : subset_R) (M : ℝ),
    (∀ (L : ℝ), L < M ⇒ ∃ a : A, L < a)
       ⇒ ∀ (K : ℝ), is_upper_bound A K ⇒ M ≤ K.
Proof.
Take A : subset_R and M : ℝ.
Assume that (∀ L : ℝ, L < M ⇒ there exists a : A, L < a) (i).
Take K : ℝ.
Assume that (is_upper_bound A K) (ii).
Expand the definition of is_upper_bound in (ii).
That is, write (ii) as
  (∀ a : A, a ≤ K).
We need to show that (M ≤ K).
We argue by contradiction.
Assume that (¬ M ≤ K).
It holds that (M > K).
By (i) it holds that (∃ a : A, K < a) (iii).
Obtain a according to (iii), so for a : A it holds that (K < a).
By (ii) it holds that (a ≤ K).
It holds that (K < K).
It holds that (¬ (K < K)).
Contradiction.
Qed.

Lemma if_almost_minimizer_then_every_low_bd_smaller :
  ∀ (A : subset_R) (m : ℝ),
    (∀ (L : ℝ), L > m ⇒ ∃ a : A, L > a)
       ⇒ ∀ (K : ℝ), is_lower_bound A K ⇒ K ≤ m.
Proof.
Take A : subset_R and m : ℝ.
Assume that (∀ L : ℝ, L > m ⇒ there exists a : A, L > a) (i).
Take K : ℝ.
Assume that (is_lower_bound A K) (ii).
Expand the definition of is_lower_bound in (ii).
That is, write (ii) as
  (∀ a : A, K ≤ a).
We need to show that (K ≤ m).
We argue by contradiction.
Assume that (¬ K ≤ m).
It holds that (K > m).
By (i) it holds that (∃ a : A, K > a) (iii).
Obtain a according to (iii), so for a : A it holds that (K > a).
By ii it holds that (K ≤ a).
It holds that (K > K).
It holds that (¬ (K > K)).
Contradiction.
Qed.

Lemma if_almost_maximizer_ε_then_every_upp_bd_larger :
  ∀ (A : subset_R) (M : ℝ),
    (∀ (ε : ℝ), ε > 0 ⇒ ∃ a : A, M - ε < a)
       ⇒ ∀ (K : ℝ), is_upper_bound A K ⇒ M ≤ K.
Proof.
Take A : subset_R and M : ℝ.
Assume that (for all ε : ℝ, ε > 0 ⇨ there exists a : A, M - ε < a) (i).
By if_almost_maximizer_then_every_upp_bd_larger it suffices to show that 
  (for all L : ℝ, L < M ⇨ there exists a : A, L < a).
Take L : ℝ; such that (L < M).
It holds that (M - L > 0).
Define ε1 := (M - L).
It holds that (ε1 > 0).
By (i) it holds that (there exists a : A , M - ε1 < a) (ii).
Obtain a0 according to (ii), so for a : A it holds that (M - ε1 < a).
Choose a := a0.
We conclude that (& L &= M - (M - L) &= M - ε1 &< a0 &= a).
Qed.

Lemma if_almost_minimizer_ε_then_every_low_bd_smaller :
  ∀ (A : subset_R) (m : ℝ),
    (∀ (ε : ℝ), ε > 0 ⇒ ∃ a : A, m + ε > a)
       ⇒ ∀ (K : ℝ), is_lower_bound A K ⇒ K ≤ m.
Proof.
Take A : subset_R and m : ℝ.
Assume that (for all ε : ℝ, ε > 0 ⇨ there exists a : A, m + ε > a) (i).
By if_almost_minimizer_then_every_low_bd_smaller it suffices to show that
  (for all L : ℝ, L > m ⇨ there exists a : A, L > a).
Take L : ℝ; such that (L > m).
It holds that (L - m > 0).
Define ε1 := (L - m).
It holds that (ε1 > 0).
By (i) it holds that (there exists a : A , m + ε1 > a) (ii).
Obtain a0 according to (ii), so for a0 : A it holds that (m + ε1 > a0).
Choose a := a0.
We need to show that (a < L).
We conclude that (& a &= a0 &< m + ε1 &= m + L - m &= L).
Qed.

Lemma exists_almost_maximizer_ε :
  ∀ (A : subset_R) (M : ℝ),
    is_sup A M ⇒
      ∀ (ε : ℝ), ε > 0 ⇒ 
        ∃ a : A, M - ε < a.
Proof.
    Take A : (subset_R).
    Take M : ℝ.
    Assume that (is_sup A M).
    Take ε : ℝ; such that (ε > 0).
    It holds that (M - ε < M).
    (** TODO: fix this *)
    apply exists_almost_maximizer with (L := M- ε) (M := M).
    - We conclude that (is_sup A M).
    - We conclude that (M - ε < M).
Qed.

Lemma exists_almost_minimizer_ε :
  ∀ (A : subset_R) (m : ℝ),
    is_inf A m ⇒
      ∀ (ε : ℝ), ε > 0 ⇒ 
        ∃ a : A, m + ε > a.
Proof.
    Take A : (subset_R).
    Take m : ℝ.
    Assume that (is_inf A m).
    Take ε : ℝ; such that (ε > 0).
    It holds that (m + ε > m).
    (** TODO: fix this *)
    apply exists_almost_minimizer with (L := m + ε) (m := m).
    - We conclude that (is_inf A m).
    - We conclude that (m + ε > m).
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
Take A : subset_R and M : ℝ.
We show both directions.
- We need to show that (is_sup A M ⇨ is_sup_alt_char A M).
  Assume that (is_sup A M) (i).
  Expand the definition of is_sup_alt_char.
  That is, write the goal as (
  is_upper_bound A M
  ∧ (for all ε : ℝ,
     ε > 0 ⇨ there exists a : A ,
               M - ε < a) ).
  We show both statements.
  + We need to show that (is_upper_bound A M).
    Expand the definition of is_sup in (i).
    That is, write (i) as (
    is_upper_bound A M
     ∧ (for all M0 : ℝ,
      is_upper_bound A M0 ⇨ M ≤ M0) ).
    Because (i) both (is_upper_bound A M) and
      (for all M0 : ℝ, is_upper_bound A M0 ⇨ M ≤ M0) hold.
    It follows that (is_upper_bound A M).

  + We need to show that (for all ε : ℝ, ε > 0 ⇨ there exists a : A, M - ε < a ).
    By exists_almost_maximizer_ε we conclude that
   (  for all ε : ℝ,
      ε > 0 ⇨ there exists a : A ,
            M - ε < a).

- We need to show that (is_sup_alt_char A M ⇨ is_sup A M).
  Assume that (is_sup_alt_char A M) (i).
  Expand the definition of is_sup_alt_char in (i).
  That is, write (i) as (
  is_upper_bound A M
   ∧ (for all ε : ℝ,
     ε > 0 ⇨ there exists a : A ,
               M - ε < a) ).
  Because (i) both (is_upper_bound A M) (ii) and
    (for all ε : ℝ, ε > 0 ⇨ there exists a : A, M - ε < a) hold.

  Expand the definition of is_sup.
  That is, write the goal as (
  is_upper_bound A M
  ∧ (for all M0 : ℝ,
     is_upper_bound A M0 ⇨ M ≤ M0) ).
  We show both statements.
  + We need to show that (is_upper_bound A M).
    By (ii) we conclude that (is_upper_bound A M).
  + We need to show that (for all M0 : ℝ, is_upper_bound A M0 ⇨ M ≤ M0).
    By if_almost_maximizer_ε_then_every_upp_bd_larger
    we conclude that (for all M0 : ℝ,
    is_upper_bound A M0 ⇨ M ≤ M0).
Qed.

Theorem alt_char_inf :
  ∀ (A : subset_R) (m : ℝ),
    is_inf A m ⇔ is_inf_alt_char A m.
Proof.
Take A : subset_R and m : ℝ.
We show both directions.
- We need to show that (is_inf A m ⇨ is_inf_alt_char A m).
  Assume that (is_inf A m) (i).
  Expand the definition of is_inf_alt_char.
  That is, write the goal as (
  is_lower_bound A m
  ∧ (for all ε : ℝ,
     ε > 0 ⇨ there exists a : A ,
               m + ε > a) ).
  We show both statements.
  + We need to show that (is_lower_bound A m).
    Expand the definition of is_inf in (i).
    That is, write (i) as (
    is_lower_bound A m ∧ (for all l : ℝ,
                        is_lower_bound A l ⇨ l ≤ m) 
    ).
    Because (i) both (is_lower_bound A m) and
      (for all l : ℝ, is_lower_bound A l ⇨ l ≤ m) hold.
    It follows that (is_lower_bound A m).

  + We need to show that (for all ε : ℝ, ε > 0 
      ⇨ there exists a : A, m + ε > a).
    By exists_almost_minimizer_ε we conclude that
    (for all ε : ℝ,
       ε > 0 ⇨ there exists a : A ,
            m + ε > a).

- We need to show that (is_inf_alt_char A m ⇨ is_inf A m).
  Assume that (is_inf_alt_char A m) (i).
  Expand the definition of is_inf_alt_char in (i).
  That is, write (i) as (
    is_lower_bound A m
     ∧ (for all ε : ℝ,
     ε > 0 ⇨ there exists a : A ,
               m + ε > a) ).
  Because (i) both (is_lower_bound A m) (ii) and
    (for all ε : ℝ, ε > 0 ⇨ there exists a : A, m + ε > a) hold.

  Expand the definition of is_inf.
  That is, write the goal as (
    is_lower_bound A m ∧ (for all l : ℝ,
                        is_lower_bound A l ⇨ l ≤ m)
   ).
  We show both statements.
  + We need to show that (is_lower_bound A m).
    By (ii) we conclude that (is_lower_bound A m).
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
    Assume that (is_sup A M).
    We argue by contradiction.
    Assume that (¬ (A M ∨ (for all a : A, a < M))).
    It holds that ((¬ (A M)) ∧ 
      ¬(∀ a : A, a < M)) (i).
    Because (i) both(¬ (A M)) and (¬(∀ a : A, a < M)) hold.
    We claim that (for all a : A, a < M).
    { 
      Take a : A.
      By sup_is_upp_bd it holds that (is_upper_bound A M).
      It holds that (a ≤ M).
      We claim that (M ≠ a).
      {
        Assume that (M = a) (ii).
        We claim that (A M).
        { It holds that (A a) (iii).
          (* TODO: We conclude that (A M). should work *)
          exact (eq_ind_r (fun x => A x) (iii) (ii)).
        }
        Contradiction.
      }
      We conclude that (a < M).
    }
    Contradiction.
Qed.

(** * Lemmas for convenience*)
Lemma bounded_by_upper_bound_propform :
  ∀ (A : subset_R) (M : ℝ) (b : ℝ),
    is_upper_bound A M ⇒ A b ⇒ b ≤ M.
Proof.
    Take A : subset_R.
    Take M : ℝ.
    Take b : ℝ.
    Assume that (is_upper_bound A M) (i).
    Assume that (A b) (ii).
    Define c := (mk_elem_R A b (ii)).
    Expand the definition of is_upper_bound in (i).
    That is, write (i) as (for all a : A, a ≤ M).
    By (i) it holds that (c ≤ M).
    We conclude that (b ≤ M).
Qed.

Lemma bounded_by_lower_bound_propform :
  ∀ (A : subset_R) (m : ℝ) (b : ℝ),
    is_lower_bound A m ⇒ A b ⇒ m ≤ b.
Proof.
    Take A : subset_R.
    Take m : ℝ.
    Take b: ℝ.
    Assume that (is_lower_bound A m) (i).
    Assume that (A b) (ii).
    Define c := (mk_elem_R A b (ii)).
    Expand the definition of is_lower_bound in (i).
    That is, write (i) as (for all a : A, m ≤ a).
    By (i) it holds that (m ≤ c).
    We conclude that (m ≤ b).
Qed.

Global Hint Resolve bounded_by_upper_bound_propform : reals.
Global Hint Resolve bounded_by_lower_bound_propform : reals.
Global Hint Resolve alt_char_inf : reals.
Global Hint Resolve alt_char_sup : reals.
Global Hint Resolve <- alt_char_inf : reals.
Global Hint Resolve <- alt_char_sup : reals.

(** ### **Hints***)
Global Hint Unfold is_sup : reals.
Global Hint Unfold is_inf : reals.
Global Hint Unfold is_upper_bound : reals.
Global Hint Unfold is_lower_bound :reals.
