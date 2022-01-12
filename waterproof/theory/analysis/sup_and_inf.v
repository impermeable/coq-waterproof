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
(*
Require Import Classical.
Require Import Classical_Prop.
Require Import Classical_Pred_Type.
*)

Require Import Waterproof.AllTactics.
Require Import Waterproof.load_database.RealsAndIntegers.
Require Import Waterproof.notations.notations.
Require Import Waterproof.set_search_depth.To_5.
Require Import Waterproof.load_database.Intuition.
Require Import Waterproof.load_database.ClassicalLogic.
Require Import Coq.Logic.Classical.

Definition is_in {D : Set} := fun (A : (D → Prop)) ↦ (fun (x : D) ↦ A x).
Notation "x ∈ A" := (@is_in _ A x) (at level 50) : sup_and_inf_scope.
(** ## Suprema and infima*)
Notation is_sup := is_lub.
Notation is_bdd_above := bound.
Open Scope sup_and_inf_scope.

(** ## Upper bounds

A number $M : ℝ$ is called an **upper bound** of a subset $A : ℝ \to \mathsf{Prop}$ of the real numbers, if for all $a : ℝ$, if $a ∈ A$ then $a ≤ M$.

```
Definition is_upper_bound (A : ℝ → Prop) (M : ℝ) :=
  ∀ a : A, a ∈ A ⇒ a ≤ M.
```

We say that a subset $A : ℝ \to \mathsf{Prop}$ is bounded above if there exists an $M : ℝ$ such that $M$ is an upper bound of $A$.

```
Definition is_bounded_above (A : ℝ → Prop) :=
  ∃ M : ℝ, is_upper_bound A M.
```

## The supremum

A real number $L : ℝ$ is called the **supremum** of a subset $A : ℝ \to \mathsf{Prop}$ if it is the smallest upper bound.
```
Definition is_sup (A : ℝ → Prop) (L : ℝ) :=
  (is_upper_bound A L) ∧ (∀ M : ℝ, is_upper_bound A M ⇒ (L ≤ M) ).
```

## The completeness axiom

The completeness axiom of the real numbers says that when a subset $A$ of the real numbers is bounded from above, and when there exists an element in the set, then there exists an $L$ such that $L$ is the supremum of $A$.

```
Axiom completeness : ∀ A : ℝ → Prop,
      is_bounded_above A ⇒ 
        ((∃ x : ℝ, x ∈ A) ⇒ { M : ℝ | is_sup A M }).
```*)
(** ## Lower bounds

A number $m : ℝ$ is called a lower bound of a subset $A : ℝ → \mathsf{Prop}$, if for all $a : \mathbb{R}$, if $a \in A$ then $a ≥ m$.*)
Definition is_lower_bound (A : ℝ → Prop) (m : ℝ) :=
  ∀ a : ℝ, a ∈ A ⇒ m ≤ a.
(** We say that a subset $A : ℝ → \mathsf{Prop}$ is bounded below if there exists an $m : ℝ$ such that $m$ is a lower bound of $A$.*)
Definition is_bdd_below (A : ℝ → Prop) :=
  ∃ m : ℝ, is_lower_bound A m.
(** ## The infimum

A real number $m : ℝ$ is called the **infimum** of a subset $A : ℝ → \mathsf{Prop}$ if it is the largest lower bound.*)
Definition is_inf :=
  fun (A : ℝ → Prop) m 
    ↦ (is_lower_bound A m) ∧ (∀ l : ℝ, is_lower_bound A l ⇒ l ≤ m).
(** ## Reflection of a subset of ℝ in the origin

Before we continue showing properties of the infimum, we first introduce the reflection of subsets of $\mathbb{R}$ in the origin. Given a subset $A : ℝ → \mathsf{Prop}$, we consider the set $-A$ (which we write as $\mathsf{set\_opp} A$), defined by*)
Definition set_opp (A : ℝ → Prop)  :=
  fun (x : ℝ) ↦ (A (-x)).

Lemma upp_bd_set_to_low_bd_set_opp :
  ∀ (A : ℝ → Prop) (M : ℝ),
    is_upper_bound A M ⇒ 
      is_lower_bound (set_opp A) (-M).
Proof.
    Take A : (ℝ → Prop). 
    Take M : ℝ.
    Assume (is_upper_bound A M) (i).
    Expand the definition of is_lower_bound.
    That is, write the goal as (for all a : ℝ, a ∈ set_opp A ⇨ -M ≤ a).
    We need to show that (∀ a : ℝ, (-a ∈ A) ⇒ -M ≤ a).
    Take a : ℝ. 
    Assume (-a ∈ A).
    By i it holds that H1 : (-a ≤ M).
    It follows that (-M ≤ a).
Qed.

Lemma low_bd_set_to_upp_bd_set_opp :
  ∀ (A : ℝ → Prop) (m : ℝ),
    is_lower_bound A m ⇒
      is_upper_bound (set_opp A) (-m).
Proof.
    Take A : (ℝ → Prop).
    Take m : ℝ.
    Assume (is_lower_bound A m) (i).
    Expand the definition of is_upper_bound.
    That is, write the goal as (for all x : ℝ, set_opp A x ⇨ x ≤ -m).
    We need to show that (∀ a : ℝ, (-a ∈ A) ⇒ a ≤ -m).
    Take a : ℝ. 
    Assume (-a ∈ A).
    By i it holds that H1 : (m ≤ -a).
    It follows that (a ≤ -m).
Qed.

Lemma low_bd_set_opp_to_upp_bd_set :
  ∀ (A : ℝ → Prop) (m : ℝ),
    is_lower_bound (set_opp A) m ⇒ 
      is_upper_bound A (-m).
Proof.
    Take A : (ℝ → Prop). 
    Take m : ℝ.
    Assume (is_lower_bound (set_opp A) m).
    Expand the definition of is_upper_bound.
    That is, write the goal as (for all x : ℝ, A x ⇨ x ≤ - m).
    Take a : ℝ.
    Assume (a ∈ A) (i).
    It holds that m_low_bd_2 : (for all x : R, (-x) ∈ A -> m <= x).
    We claim that minmin_a_in_A : (--a ∈ A).
    { It holds that nna_eq_a  :(--a = a).
      (* TODO: We conclude that (--a ∈ A). should work *)
      exact (eq_ind_r (fun x => x ∈ A) (i) nna_eq_a).
    }
    It holds that m_le_min_a : (m ≤ -a).
    It follows that (a ≤ -m).
Qed.

Lemma upp_bd_set_opp_to_low_bd_set :
  ∀ (A : ℝ → Prop) (M : ℝ),
    is_upper_bound (set_opp A) M ⇒
      is_lower_bound A (-M).
Proof.
    Take A : (ℝ → Prop).
    Take M : ℝ.
    Assume (is_upper_bound (set_opp A) M).
    Expand the definition of is_lower_bound.
    That is, write the goal as (for all a : ℝ, a ∈ A ⇨ - M ≤ a).
    Take a : ℝ.
    Assume (a ∈ A) (i).
    We claim that minmin_a_in_A : (--a ∈ A).
    { It holds that nna_eq_a  :(--a = a).
      (* TODO: We conclude that (--a ∈ A). should work *)
      exact (eq_ind_r (fun x => x ∈ A) (i) nna_eq_a).
    }
    It holds that min_a_le_M : (-a ≤ M).
    It follows that (-M ≤ a).
Qed.


Lemma bdd_below_to_bdd_above_set_opp :
  ∀ (A : ℝ → Prop),
    is_bdd_below A ⇒ is_bdd_above (set_opp A).
Proof.
    Take A : (ℝ → Prop).
    Assume (is_bdd_below A) (i).
    We need to show that (∃ M : ℝ, is_upper_bound (set_opp A) M).
    Expand the definition of is_bdd_below in i.
    That is, write i as (∃ m : ℝ, is_lower_bound A m).
    Choose m such that m_is_lower_bd_A according to i.
    Choose M := (-m).
    We need to show that (is_upper_bound (set_opp A) M).
    By low_bd_set_to_upp_bd_set_opp we conclude that (is_upper_bound (set_opp A) M).
Qed.


Lemma sup_set_opp_is_inf_set :
  ∀ (A : ℝ → Prop) (M : ℝ),
    is_sup (set_opp A) M ⇒ is_inf A (-M).
Proof.
    Take A : (ℝ → Prop).
    Take M : ℝ.
    Assume (is_sup (set_opp A) M) (i).
    Expand the definition of is_inf.
    That is, write the goal as (is_lower_bound A (- M) 
      ∧ (for all l : ℝ, is_lower_bound A l ⇨ l ≤ - M)).
    We show both statements.
    - We need to show that ( is_lower_bound A (- M) ).
      Expand the definition of is_lub in i.
      That is, write i as (is_upper_bound (set_opp A) M 
        ∧ (for all b : ℝ, is_upper_bound (set_opp A) b ⇨ M ≤ b)).
      Choose M_upp_bd such that H1 according to i.
      By upp_bd_set_opp_to_low_bd_set we conclude that (is_lower_bound A (-M)).
    - We need to show that (∀ l : ℝ, is_lower_bound A l ⇒ l ≤ -M).
      Expand the definition of is_lower_bound.
      That is, write the goal as (for all l : ℝ, (for all a : ℝ, a ∈ A ⇨ l ≤ a) ⇨ l ≤ - M).
      Take l : ℝ.
      Assume (is_lower_bound A l).
      Expand the definition of is_lub in i.
      That is, write i as (is_upper_bound (set_opp A) M 
        ∧ (for all b : ℝ, is_upper_bound (set_opp A) b ⇨ M ≤ b)).
      Because i both previously_proven and H1.
      By low_bd_set_to_upp_bd_set_opp it holds that H2 : (is_upper_bound (set_opp A) (-l)).
      By H1 it holds that H3 : (M ≤ -l).
      We conclude that (l <= -M).
Qed.

Lemma exists_inf :
  ∀ A : (ℝ →  Prop), is_bdd_below A ⇒
    ((∃ x : ℝ, x ∈ A) ⇒ { m : ℝ | is_inf A m }).
Proof.
    Take A : (ℝ → Prop).
    Assume (is_bdd_below A).
    Assume (∃ x : ℝ, x ∈ A) (i).
    Define B := (set_opp A).
    Expand the definition of set_opp in B.
    That is, write B as (ℝ ⇨ Prop).
    We claim that H : (for all s : ℝ, (A s) -> (B (-s))).
    { Take s : ℝ.
      Assume (A s).
      (* TODO: make nicer *)
      We need to show that (A (--s)).
      It holds that H2 : (A (--s) = A s).
      Fail We conclude that (A (--s)).
      rewrite H2.
      We conclude that (A s).
    }
    By bdd_below_to_bdd_above_set_opp it holds that B_bdd_above : (is_bdd_above B).
    We claim that ex_y_in_B : (∃ y : ℝ, y ∈ B).
    { Choose x such that x_in_A according to i.
      Choose y := (-x).
      We need to show that (B (-x)).
      By H we conclude that (B (-x)).
    }
    By completeness it holds that exists_sup : ({L | is_sup B L}).
    Choose L such that L_is_sup according to exists_sup.
    By sup_set_opp_is_inf_set it holds that minL_is_inf_A : (is_inf A (-L)).
    We conclude that ({m : ℝ | is_inf A m}). (*TODO: make solvable with 'Choose ...'.*)
Qed.



(** ### A supremum is an upper bound

If $M$ is the supremum of a set $A$, it is also an upper bound.*)
Lemma sup_is_upp_bd :
  ∀ A : ℝ → Prop,
    ∀ M : ℝ,
      is_sup A M ⇒ is_upper_bound A M.
Proof.
    Take A : (ℝ → Prop) and M : ℝ. 
    Assume (is_sup A M).
    It holds that M_is_sup_A_2 : (is_upper_bound A M ∧ (∀ b: ℝ, is_upper_bound A b ⇒ M ≤ b)).
    Because M_is_sup_A_2 both part1 and part2.
    It follows that (is_upper_bound A M). 
Qed.


(** ### Any upper bound is greater than or equal to the supremum*)
Lemma any_upp_bd_ge_sup :
  ∀ A : ℝ → Prop,
    ∀ M L : ℝ,
      is_sup A M ⇒ (is_upper_bound A L ⇒ M ≤ L).
Proof.
    Take A : (ℝ → Prop) and M, l : ℝ.
    Assume (is_sup A M) (i) and (is_upper_bound A l).
    Because i both M_is_upp_bd and any_upp_bd_le_M.
    (** We need to show that $M \leq L$.*)
    We conclude that (M <= l).
Qed.



(** ## Infima*)
(** ## An infimum is a lower bound*)
Lemma inf_is_low_bd :
  ∀ A : ℝ → Prop,
    ∀ m : ℝ,
      is_inf A m ⇒ is_lower_bound A m.
Proof.
    Take A : (ℝ → Prop) and m : R.
    Assume (is_inf A m) (i).
    Because i both m_is_low_bd and any_low_bd_ge_m.
    We conclude that (is_lower_bound A m).
    (** to show that $m$ is a lower bound of $A$*)
Qed.


(** ## Any lower bound is less than or equal to the infimum*)
Lemma any_low_bd_ge_inf :
  ∀ A : ℝ → Prop,
    ∀ m l : ℝ,
      is_inf A m ⇒ is_lower_bound A l ⇒ l ≤ m.
Proof.
    Take A : (R → Prop) and m, l : R.
    Assume (is_inf A m) (i) and (is_lower_bound A l).
    Because i both m_low_bd and any_low_bd_le_m.
    By any_low_bd_le_m we conclude that (l ≤ m).
Qed.

(** ### $\varepsilon$-characterizations*)
Lemma exists_almost_maximizer :
  ∀ (A : ℝ -> Prop) (M : ℝ),
    is_sup A M ⇒
      ∀ (L : ℝ), L < M ⇒ 
        ∃ a : ℝ, A a ∧ L < a.
Proof.
    Take A : (ℝ -> Prop) and M : ℝ.
    Assume (is_sup A M).
    Take L : ℝ. 
    Assume (L < M).
    We argue by contradiction.
    Assume (¬ (there exists a : ℝ, A a ∧ L < a)).
    It holds that H0 : (∀ x : ℝ, A x ⇒ ¬(L < x)).
    We claim that H3 : (is_upper_bound A L).
    { We need to show that (∀ x : ℝ, A x ⇒ (x <= L)).
      Take x : R.
      Assume (A x).
      It holds that not_L_lt_x : (~ L < x).
      We conclude that (x ≤ L).
    }
    By any_upp_bd_ge_sup it holds that H4 : (M ≤ L).
    It holds that H5 : (¬(M ≤ L)).
    Contradiction.
Qed.


Lemma exists_almost_maximizer_ε :
  ∀ (A : ℝ -> Prop) (M : ℝ),
    is_sup A M ⇒
      ∀ (ε : ℝ), ε > 0 ⇒ 
        ∃ a : ℝ, A a ∧ M - ε < a.
Proof.
    Take A : (ℝ -> Prop) and M : ℝ.
    Assume (is_sup A M).
    Take ε : ℝ; such that (ε > 0).
    It holds that H1 : (M - ε < M). 
    apply exists_almost_maximizer with (L := M- ε) (M := M).
    - We conclude that (is_sup A M).
    - We conclude that (M - ε < M).
Qed.


Lemma max_or_strict :
  ∀ (A : ℝ → Prop) (M : ℝ),
    is_sup A M ⇒ 
      (A M) ∨ (∀ a : ℝ, A a ⇒ a < M).
Proof.
    Take A : (ℝ → Prop) and M : ℝ.
    Assume (is_sup A M).
    We argue by contradiction.
    Assume ( ¬ (A M ∨ (for all a : ℝ, A a ⇨ a < M))).
    It holds that H1 : ((¬ (A M)) ∧ ¬(∀ a : ℝ, A a ⇒ a < M) ).
    Because H1 both H2 and H3.
    (** We only show the proposition on the *)
    (** hand side of the or-sign, i.e. we will show that for all $a \in \mathbb{R}$, if $a \in A$ then $a < M$*)
    We claim that H4 : (∀ a : ℝ, A a ⇒ a < M).
    {
    Take a : ℝ.
    Assume (A a).
    By sup_is_upp_bd it holds that M_upp_bd : (is_upper_bound A M).
    It holds that a_le_M : (a ≤ M).
    We claim that a_is_not_M : (¬(a = M)).
    Assume (a = M) (eq_1).
    We claim that M_in_A : (A M).
    { (* TODO: improve*)
      rewrite <- eq_1.
      We conclude that (A a).
    }
    Contradiction.
    We conclude that (a < M).
    }
    Contradiction.
Qed.


(** ## Suprema and sequences*)
Lemma seq_ex_almost_maximizer_ε :
  ∀ (a : ℕ → ℝ) (pr : has_ub a) (ε : ℝ), 
    ε > 0 ⇒ ∃ k : ℕ, a k > lub a pr - ε.
Proof.
    Take a : (ℕ → ℝ).
    Assume (has_ub a) (i).
    Expand the definition of lub.
    That is, write the goal as (for all ε : ℝ,  ε > 0 
      ⇨ there exists k : ℕ, a k > (let (a0, _) := ub_to_lub a (i) in a0) - ε).
    Define sup_with_proof := (ub_to_lub a (i)).
    Choose l such that l_is_sup according to sup_with_proof.
    Take ε : ℝ; such that (ε > 0).
    By exists_almost_maximizer_ε it holds that H1 : (∃ y : ℝ, (EUn a) y ∧ y > l - ε).
    Choose y such that H2 according to H1.
    Because H2 both y_in_range and y_gt_l_min_ε.
    Expand the definition of EUn in y_in_range.
    That is, write y_in_range as (there exists i : ℕ , y = a i).
    Choose n such that an_is_y according to y_in_range.
    Choose k := n.
    We need to show that (l - ε < a n).
    We conclude that (& l - ε &< y &= a n).
Qed.


Lemma seq_ex_almost_maximizer_m :
  ∀ (a : ℕ → ℝ) (pr : has_ub a) (m : ℕ), 
    ∃ k : ℕ, a k > lub a pr - 1 / (INR(m) + 1).
Proof.
    Take a : (ℕ → ℝ).
    Assume (has_ub a).
    Take m : ℕ.
    By seq_ex_almost_maximizer_ε it suffices to show that (1 / (m + 1) > 0).
    (** We need to show that $1/(m+1) > 0$.*)
    It holds that m_plus_1_gt_0 : (0 < m + 1)%R.
    We conclude that (1 / (m+1) > 0).
Qed.


Lemma exists_almost_lim_sup_aux :
  ∀ (a : ℕ → ℝ) (pr : has_ub a) (m : ℕ) (N : ℕ),
    ∃ k : ℕ, (k ≥ N)%nat ∧ a k > sequence_ub a pr N - 1 / (INR(m) + 1).
Proof.
    Take a : (ℕ → ℝ).
    Assume (has_ub a) (i).
    Take m, Nn : ℕ.
    By seq_ex_almost_maximizer_m it holds that
      H1 : (∃ k : ℕ, a (Nn + k)%nat > sequence_ub a (i) Nn - 1 / (INR m + 1)).
    Choose k such that k_good according to H1.
    Choose l := (Nn+k)%nat.
    We show both statements.
    - We need to show that ( (l ≥ Nn)%nat ).
      We conclude that ((l ≥ Nn)%nat).
    - We need to show that ( a l > sequence_ub a (i) Nn - 1 / (m + 1) ).
      We conclude that ( a l > sequence_ub a (i) Nn - 1 / (m + 1) ).
Qed.
