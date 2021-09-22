(** # Suprema and infima*)
Require Import Reals.
Require Import Lra.
Require Import Classical.
Require Import Classical_Prop.
Require Import Classical_Pred_Type.

Require Import Waterproof.AllTactics.
Require Import Waterproof.contradiction_tactics.basic_contradiction.
Require Import Waterproof.selected_databases.
Require Import Waterproof.load_database.All.
Require Import Waterproof.notations.notations.
Require Import Waterproof.set_search_depth.To_5.
Require Import Waterproof.set_intuition.Enabled.
Require Import Waterproof.contradiction_tactics.basic_contradiction.

Open Scope analysis_scope.
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
    Assume M_upp_bd : (is_upper_bound A M).
    Expand the definition of is_lower_bound.
    We need to show that (∀ a : ℝ, (-a ∈ A) ⇒ -M ≤ a).
    Take a : ℝ. 
    Assume min_a_in_A : (-a ∈ A).
    By M_upp_bd it holds that H1 : (-a ≤ M).
    It follows that (-M ≤ a).
Qed.

Lemma low_bd_set_to_upp_bd_set_opp :
  ∀ (A : ℝ → Prop) (m : ℝ),
    is_lower_bound A m ⇒
      is_upper_bound (set_opp A) (-m).
Proof.
    Take A : (ℝ → Prop). 
    Take m : ℝ.
    Assume m_low_bd : (is_lower_bound A m).
    Expand the definition of is_upper_bound.
    We need to show that (∀ a : ℝ, (-a ∈ A) ⇒ a ≤ -m).
    Take a : ℝ. 
    Assume min_a_in_A : (-a ∈ A).
    By m_low_bd it holds that H1 : (m ≤ -a).
    It follows that (a ≤ -m).
Qed.

Lemma low_bd_set_opp_to_upp_bd_set :
  ∀ (A : ℝ → Prop) (m : ℝ),
    is_lower_bound (set_opp A) m ⇒ 
      is_upper_bound A (-m).
Proof.
    Take A : (ℝ → Prop). 
    Take m : ℝ.
    Assume m_low_bd : (is_lower_bound (set_opp A) m).
    Expand the definition of is_upper_bound.
    We need to show that (∀ a : ℝ, a ∈ A ⇒ a ≤ -m).
    Take a : ℝ.
    Assume a_in_A : (a ∈ A).
    Write m_low_bd as (∀ a : ℝ, (-a) ∈ A ⇒ m ≤ a).
    We claim that minmin_a_in_A : (--a ∈ A).
    Write goal using (--a = a) as (a ∈ A).
    Apply a_in_A.
    By m_low_bd it holds that m_le_min_a : (m ≤ -a).
    It follows that (a ≤ -m).
Qed.

Lemma upp_bd_set_opp_to_low_bd_set :
  ∀ (A : ℝ → Prop) (M : ℝ),
    is_upper_bound (set_opp A) M ⇒
      is_lower_bound A (-M).
Proof.
    Take A : (ℝ → Prop).
    Take M : ℝ.
    Assume M_upp_bd : (is_upper_bound (set_opp A) M).
    Expand the definition of is_lower_bound.
    We need to show that (∀ a : ℝ, a ∈ A ⇒ -M ≤ a).
    Take a : ℝ.
    Assume a_in_A : (a ∈ A).
    We claim that minmin_a_in_A : (--a ∈ A).
    Write goal using (--a = a) as (a ∈ A).
    Apply a_in_A.
    By M_upp_bd it holds that min_a_le_M : (-a ≤ M).
    It follows that (-M ≤ a).
Qed.


Lemma bdd_below_to_bdd_above_set_opp :
  ∀ (A : ℝ → Prop),
    is_bdd_below A ⇒ is_bdd_above (set_opp A).
Proof.
    Take A : (ℝ → Prop).
    Assume A_bdd_below : (is_bdd_below A).
    We need to show that (∃ M : ℝ, is_upper_bound (set_opp A) M).
    Write A_bdd_below as (∃ m : ℝ, is_lower_bound A m).
    Choose m such that m_low_bd according to A_bdd_below.
    Expand the definition of bound.
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
    Assume M_is_sup : (is_sup (set_opp A) M).
    Expand the definition of is_inf.
    We need to show that (is_lower_bound A (-M) ∧ ∀ l : ℝ, is_lower_bound A l ⇒ l ≤ -M).
    We show both statements.
    Expand the definition of is_lub in M_is_sup.
    Choose M_upp_bd such that H1 according to M_is_sup.
    By upp_bd_set_opp_to_low_bd_set we conclude that (is_lower_bound A (-M)).
    We need to show that (∀ l : ℝ, is_lower_bound A l ⇒ l ≤ -M).
    Expand the definition of is_lower_bound.
    Take l : ℝ.
    Assume l_low_bd : (is_lower_bound A l).
    Expand the definition of is_lub in M_is_sup.
    destruct M_is_sup as [previously_proven H1].
    By low_bd_set_to_upp_bd_set_opp it holds that H2 : (is_upper_bound (set_opp A) (-l)).
    By H1 it holds that H3 : (M ≤ -l).
    This concludes the proof.
Qed.

Ltac2 Eval global_database_selection.

Lemma exists_inf :
  ∀ A : (ℝ →  Prop), is_bdd_below A ⇒
    ((∃ x : ℝ, x ∈ A) ⇒ { m : ℝ | is_inf A m }).
Proof.
    Take A : (ℝ → Prop).
    Take A_bdd_below : (is_bdd_below A).
    Assume ex_x : (∃ x : ℝ, x ∈ A).
    Define B := (set_opp A).
    Expand the definition of set_opp in B.
    We claim that H : (for all s : ℝ, (A s) -> (B (-s))).
    Take s : ℝ.
    Assume A_s_true : (A s).
    Rewrite using (B (-s) = A (--s)).
    Rewrite using (--s = s).
    Apply A_s_true.
    We claim that B_bdd_above : (is_bdd_above B).
    {
        Apply bdd_below_to_bdd_above_set_opp.
        This follows immediately.
    }
    We claim that ex_y_in_B : (∃ y : ℝ, y ∈ B).
    Choose x such that x_in_A according to ex_x.
    Choose y := (-x).
    We need to show that ((-(-x)) ∈ A).
    Expand the definition of is_in.
    Apply (H x).
    This follows immediately.
    By completeness it holds that exists_sup : ({L | is_sup B L}).
    Choose L such that L_is_sup according to exists_sup.
    By sup_set_opp_is_inf_set it holds that minL_is_inf_A : (is_inf A (-L)).
    This concludes the proof.
Qed.



(** ### A supremum is an upper bound

If $M$ is the supremum of a set $A$, it is also an upper bound.*)
Lemma sup_is_upp_bd :
  ∀ A : ℝ → Prop,
    ∀ M : ℝ,
      is_sup A M ⇒ is_upper_bound A M.
Proof.
    Take A : (ℝ → Prop), M : ℝ. 
    Assume M_is_sup_A : (is_sup A M).
    Write M_is_sup_A as (is_upper_bound A M ∧ (∀ b: ℝ, is_upper_bound A b ⇒ M ≤ b) ).
    Because M_is_sup_A both part1 and part2.
    It follows that (is_upper_bound A M). 
Qed.


(** ### Any upper bound is greater than or equal to the supremum*)
Lemma any_upp_bd_ge_sup :
  ∀ A : ℝ → Prop,
    ∀ M L : ℝ,
      is_sup A M ⇒ (is_upper_bound A L ⇒ M ≤ L).
Proof.
    Take A : (ℝ → Prop), M l : ℝ.
    Assume A_is_sup_M : (is_sup A M) and L_is_upp_bd_A : (is_upper_bound A l).
    Because A_is_sup_M both M_is_upp_bd and any_upp_bd_le_M.
    (** We need to show that $M \leq L$.*)
    This concludes the proof. 
Qed.



(** ## Infima*)
(** ## An infimum is a lower bound*)
Lemma inf_is_low_bd :
  ∀ A : ℝ → Prop,
    ∀ m : ℝ,
      is_inf A m ⇒ is_lower_bound A m.
Proof.
    Take A : (ℝ → Prop), m : R.
    Assume m_is_inf_A : (is_inf A m).
    Because m_is_inf_A both m_is_low_bd and any_low_bd_ge_m.
    Apply m_is_low_bd.
    (** to show that $m$ is a lower bound of $A$*)
Qed.


(** ## Any lower bound is less than or equal to the infimum*)
Lemma any_low_bd_ge_inf :
  ∀ A : ℝ → Prop,
    ∀ m l : ℝ,
      is_inf A m ⇒ is_lower_bound A l ⇒ l ≤ m.
Proof.
    Take A : (R → Prop), m l : R.
    Assume m_is_inf_A : (is_inf A m) and l_is_low_bd_A : (is_lower_bound A l).
    Because m_is_inf_A both m_low_bd and any_low_bd_le_m.
    By any_low_bd_le_m we conclude that (l ≤ m).
Qed.


Require Import Waterproof.load_database.EnableWildcard.

(** ### $\varepsilon$-characterizations*)
Lemma exists_almost_maximizer :
  ∀ (A : ℝ → Prop) (M : ℝ),
    is_sup A M ⇒
      ∀ (L : ℝ), L < M ⇒ 
        ∃ a : ℝ, A a ∧ L < a.
Proof.
    Take A : (ℝ → Prop), M : ℝ.
    Assume M_is_sup_A : (is_sup A M).
    Take L : ℝ. 
    Assume L_lt_M : (L < M).
    We argue by contradiction.
    We claim that H1 : (∀ x : ℝ, A x ⇒ x ≤ L).
    Take x : ℝ.
    Assume x_in_A : (A x).
    We claim that H_logic1 : (¬(exists a : R, (A a ∧ L < a)) -> (forall a : R, ¬((A a ∧ L < a)))).
    Apply (@not_ex_all_not ℝ (fun a : ℝ => (A a ∧ L < a))).
    By H_logic1 it holds that H_logic2 : (forall a : R, ¬((A a ∧ L < a))).
    By not_and_or it holds that H_logic3 : (forall a : R, (¬(A a) ∨ ¬(L < a))).
    Define needed_assumption := (H_logic3 x).
    Because needed_assumption either part1 or part2.
    (** case 1 *)
    Contradiction.
    (** case 2 *)
    This concludes the proof.
    It holds that H3 : (is_upper_bound A L).
    By any_upp_bd_ge_sup it holds that H4 : (M ≤ L).
    It holds that H5 : (¬(M ≤ L)).
    Contradiction.
Qed.


Lemma exists_almost_maximizer_ε :
  ∀ (A : ℝ → Prop) (M : ℝ),
    is_sup A M ⇒
      ∀ (ε : ℝ), ε > 0 ⇒ 
        ∃ a : ℝ, A a ∧ M - ε < a.
Proof.
    Take A : (ℝ → Prop), M : ℝ.
    Assume M_is_sup_A : (is_sup A M ). 
    Take ε : ℝ. 
    Assume ε_gt_0 : (ε > 0).
    It holds that H1 : (M - ε < M). 
    apply exists_almost_maximizer with (L := M- ε) (M := M).
    This follows by assumption.
    This concludes the proof.
Qed.


Lemma max_or_strict :
  ∀ (A : ℝ → Prop) (M : ℝ),
    is_sup A M ⇒ 
      (A M) ∨ (∀ a : ℝ, A a ⇒ a < M).
Proof.
    Take A : (ℝ → Prop), M : ℝ. 
    Assume M_is_sup_A : (is_sup A M). 
    We argue by contradiction. 
    By not_or_and it holds that H1 : ((¬ (A M)) ∧ ¬(∀ a : ℝ, A a ⇒ a < M) ).
    Because H1 both H2 and H3.
    (** We only show the proposition on the *)
    (** hand side of the or-sign, i.e. we will show that for all $a \in \mathbb{R}$, if $a \in A$ then $a < M$*)
    right.
    Take a : ℝ. 
    Assume a_in_A : (A a).
    By sup_is_upp_bd it holds that M_upp_bd : (is_upper_bound A M).
    It holds that a_le_M : (a ≤ M).
    We claim that a_is_not_M : (¬(a = M)).
    We argue by contradiction.
    We claim that M_in_A : (A M).
    Rewrite using (M = a).
    This follows by assumption. 
    Contradiction. 
    This concludes the proof.
Qed.


(** ## Suprema and sequences*)
Lemma seq_ex_almost_maximizer_ε :
  ∀ (a : ℕ → ℝ) (pr : has_ub a) (ε : ℝ), 
    ε > 0 ⇒ ∃ k : ℕ, a k > lub a pr - ε.
Proof.
    Take a : (ℕ → ℝ).
    Take pr : (has_ub a). 
    Expand the definition of lub.
    Define sup_with_proof := (ub_to_lub a pr).
    Choose l such that l_is_sup according to sup_with_proof.
    Take ε : ℝ. 
    Assume ε_gt_0 : (ε > 0).
    By exists_almost_maximizer_ε it holds that H1 : (∃ y : ℝ, (EUn a) y ∧ y > l - ε).
    Choose y such that H2 according to H1.
    Because H2 both y_in_range and y_gt_l_min_ε.
    Expand the definition of EUn in y_in_range.
    Choose i such that ai_is_y according to y_in_range.
    Choose k := i.
    We need to show that (a i > l - ε).
    Rewrite using (y = a i) in y_gt_l_min_ε.
    Apply y_gt_l_min_ε.
Qed.


Lemma seq_ex_almost_maximizer_m :
  ∀ (a : ℕ → ℝ) (pr : has_ub a) (m : ℕ), 
    ∃ k : ℕ, a k > lub a pr - 1 / (INR(m) + 1).
Proof.
    Take a : (ℕ → ℝ). 
    Take pr : (has_ub a). 
    Take m : ℕ.
    Apply seq_ex_almost_maximizer_ε.
    (** We need to show that $1/(m+1) > 0$.*)
     Rewrite using (1 / (INR m + 1) = / (INR m + 1)). 
    (** We need to show that $(m+1) > 0$. *)
    This follows immediately. 
Qed.


Lemma exists_almost_lim_sup_aux :
  ∀ (a : ℕ → ℝ) (pr : has_ub a) (m : ℕ) (N : ℕ),
    ∃ k : ℕ, (k ≥ N)%nat ∧ a k > sequence_ub a pr N - 1 / (INR(m) + 1).
Proof.
    Take a : (ℕ → ℝ). 
    Take pr : (has_ub a). 
    Take m Nn : ℕ.
    We claim that H1 : (∃ i : ℕ, a (Nn + i)%nat > sequence_ub a pr Nn - 1 / (INR m + 1)).
    Apply seq_ex_almost_maximizer_m.
    Choose i such that i_good according to H1.
    Choose k := (Nn+i)%nat.
    This concludes the proof.
Qed.
