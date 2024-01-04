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

Require Import Classical.
Require Import Classical_Pred_Type.
Require Import Coq.Reals.Reals.

Require Import Automation.
Require Import Notations.
Require Import Tactics.

Open Scope R_scope.

Waterproof Enable Automation RealsAndIntegers.

Notation is_bounded_above := bound.
Notation is_sup := is_lub.

(* Implement notations for these concepts. *)
Notation "M 'is' 'the' '_supremum_' 'of' A" := (is_lub A M) (at level 69).
Notation "M 'is' 'the' 'supremum' 'of' A" := (is_lub A M) (at level 69, only parsing).
Local Ltac2 unfold_is_lub (statement : constr) := eval unfold is_lub in $statement.
Ltac2 Notation "Expand" "the" "definition" "of" "supremum" "in" statement(constr) := 
  Unfold.unfold_in_statement unfold_is_lub (Some "supremum") statement.
Ltac2 Notation "_internal_" "Expand" "the" "definition" "of" "supremum" "in" statement(constr) := 
  Unfold.unfold_in_statement_no_error unfold_is_lub (Some "supremum") statement.

Notation "A 'is' '_bounded' 'from' 'above_'" := (bound A) (at level 69).
Notation "A 'is' 'bounded' 'from' 'above'" := (bound A) (at level 69, only parsing).
Local Ltac2 unfold_bound (statement : constr) := eval unfold bound in $statement.
Ltac2 Notation "Expand" "the" "definition" "of" "bounded" "from" "above" "in" statement(constr) := 
  Unfold.unfold_in_statement unfold_bound (Some "bounded from above") statement.
Ltac2 Notation "_internal_" "Expand" "the" "definition" "of" "bounded" "from" "above" "in" statement(constr) := 
  Unfold.unfold_in_statement_no_error unfold_bound (Some "bounded from above") statement.

Notation "M 'is' 'an' '_upper' 'bound_' 'for' A" := (is_upper_bound A M) (at level 69).
Notation "M 'is' 'an' 'upper' 'bound' 'for' A" := (is_upper_bound A M) (at level 69, only parsing).
Local Ltac2 unfold_is_upper_bound (statement : constr) := eval unfold is_upper_bound in $statement.
Ltac2 Notation "Expand" "the" "definition" "of" "upper" "bound" "in" statement(constr) := 
  Unfold.unfold_in_statement unfold_is_upper_bound (Some "upper bound") statement.
Ltac2 Notation "_internal_" "Expand" "the" "definition" "of" "upper" "bound" "in" statement(constr) := 
  Unfold.unfold_in_statement_no_error unfold_is_upper_bound (Some "upper bound") statement.

(** Maximum *)
Definition is_max (A : ℝ -> Prop) (x : ℝ) := (A x) ∧ (x is an upper bound for A).

Notation "M 'is' 'the' '_maximum_' 'of' A" := (is_max A M) (at level 69).
Notation "M 'is' 'the' 'maximum' 'of' A" := (is_max A M) (at level 69, only parsing).
Local Ltac2 unfold_is_max (statement : constr) := eval unfold is_max in $statement.
Ltac2 Notation "Expand" "the" "definition" "of" "maximum" "in" statement(constr) := 
  Unfold.unfold_in_statement unfold_is_max (Some "maximum") statement.
Ltac2 Notation "_internal_" "Expand" "the" "definition" "of" "maximum" "in" statement(constr) := 
  Unfold.unfold_in_statement_no_error unfold_is_max (Some "maximum") statement.


(** ## The completeness axiom

The completeness axiom of the real numbers says that when a subset $A$ of the real numbers is bounded from above, and when there exists an element in the set, then there exists an $L$ such that $L$ is the supremum of $A$.*)
Lemma R_complete : ∀ (A : ℝ → Prop) (a : ℝ),
  (A a) ⇒ (A is bounded from above) ⇒ exists M : R, M is the supremum of A.
Proof.
    Take A : (ℝ → Prop) and a : ℝ.
    Assume that (A a).
    Assume that (A is bounded from above) (i).
    We claim that (there exists x : ℝ, A x).
    { Choose (a). We conclude that (A a). }
    By completeness it holds that ({M | M is the supremum of A}).
    Obtain such an M.
    Choose (M).
    We conclude that (M is the supremum of A).
Qed.



(** 
Axiom completeness : ∀ A : ℝ → Prop,
      is_bounded_above A ⇒ 
        ((∃ x : ℝ, x ∈ A) ⇒ { M : ℝ | is_sup A M }).
```*)
(** ## Lower bounds

A number $m : ℝ$ is called a lower bound of a subset $A : ℝ → \mathsf{Prop}$, if for all $a : \mathbb{R}$, if $a \in A$ then $a ≥ m$.*)
Definition is_lower_bound (A : ℝ → Prop) (m : ℝ) :=
  ∀ a : ℝ, (A a) ⇒ m ≤ a.
(** We say that a subset $A : ℝ → \mathsf{Prop}$ is bounded below if there exists an $m : ℝ$ such that $m$ is a lower bound of $A$.*)
Definition is_bounded_below (A : ℝ → Prop) :=
  ∃ m : ℝ, is_lower_bound A m.
(** ## The infimum

A real number $m : ℝ$ is called the **infimum** of a subset $A : ℝ → \mathsf{Prop}$ if it is the largest lower bound.*)
Definition is_inf :=
  fun (A : ℝ → Prop) m 
    => (is_lower_bound A m) ∧ (∀ l : R, is_lower_bound A l ⇒ l ≤ m).

(* Implement notations for these concepts. *)
Notation "m 'is' 'the' '_infimum_' 'of' A" := (is_inf A m) (at level 69).
Notation "m 'is' 'the' 'infimum' 'of' A" := (is_inf A m) (at level 69, only parsing).
Local Ltac2 unfold_is_inf (statement : constr) := eval unfold is_inf in $statement.
Ltac2 Notation "Expand" "the" "definition" "of" "infimum" "in" statement(constr) := 
  Unfold.unfold_in_statement unfold_is_inf (Some "infimum") statement.
Ltac2 Notation "_internal_" "Expand" "the" "definition" "of" "infimum" "in" statement(constr) := 
  Unfold.unfold_in_statement_no_error unfold_is_inf (Some "infimum") statement.

Notation "A 'is' '_bounded' 'from' 'below_'" := (is_bounded_below A) (at level 69).
Notation "A 'is' 'bounded' 'from' 'below'" := (is_bounded_below A) (at level 69, only parsing).
Local Ltac2 unfold_is_bounded_below (statement : constr) := 
  eval unfold is_bounded_below in $statement.
Ltac2 Notation "Expand" "the" "definition" "of" "bounded" "from" "below" "in" statement(constr) := 
  Unfold.unfold_in_statement unfold_is_bounded_below (Some "bounded from below") statement.
Ltac2 Notation "_internal_" "Expand" "the" "definition" "of" "bounded" "from" "below" "in" statement(constr) := 
  Unfold.unfold_in_statement_no_error unfold_is_bounded_below (Some "bounded from below") statement.
  

Notation "M 'is' 'a' '_lower' 'bound_' 'for' A" := (is_lower_bound A M) (at level 69).
Notation "M 'is' 'a' 'lower' 'bound' 'for' A" := (is_lower_bound A M) (at level 69, only parsing).
Local Ltac2 unfold_is_lower_bound (statement : constr) := eval unfold is_lower_bound in $statement.
Ltac2 Notation "Expand" "the" "definition" "of" "lower" "bound" "in" statement(constr) := 
  Unfold.unfold_in_statement unfold_is_lower_bound (Some "lower bound") statement.
Ltac2 Notation "_internal_" "Expand" "the" "definition" "of" "lower" "bound" "in" statement(constr) := 
  Unfold.unfold_in_statement_no_error unfold_is_lower_bound (Some "lower bound") statement.

(** ## Reflection of a subset of ℝ in the origin

Before we continue showing properties of the infimum, 
we first introduce the reflection of subsets of $\mathbb{R}$ 
in the origin. 
Given a subset $A : ℝ → \mathsf{Prop}$, 
we consider the set $-A$ 
(which we write as $\mathsf{set\_opp} A$), defined by*)
Definition set_opp (A : ℝ -> Prop) := (fun x ↦ (A (-x))).

(** TODO: add this to additional lemmas.. *)
(** Hint Resolve neg_opp_is_original_elem : additional.*)
Lemma upp_bd_set_to_low_bd_set_opp :
  ∀ (A : ℝ → Prop) (M : ℝ),
    M is an upper bound for A ⇒ 
      is_lower_bound (set_opp A) (-M).
Proof.
    Take A : (ℝ → Prop) and M : ℝ.
    Assume that (M is an upper bound for A) (i).
    We need to show that (∀ a : ℝ, (set_opp A a) ⇒ -M ≤ a).
    Take b : ℝ. Assume that (set_opp A b).
    Define a := (-b).
    It holds that (A a).
    By (i) it holds that (a ≤ M).
    We conclude that (-M ≤ b).
Qed.

Lemma low_bd_set_to_upp_bd_set_opp :
  ∀ (A : ℝ → Prop) (m : ℝ),
    is_lower_bound A m ⇒
      -m is an upper bound for (set_opp A).
Proof.
    Take A : (ℝ → Prop) and m : ℝ.
    Assume that (is_lower_bound A m) (i).
    We need to show that (for all b : ℝ, (set_opp A b) ⇒ b ≤ -m).
    Take b : ℝ. Assume that (set_opp A b).
    Define a := (-b).
    By (i) it holds that (m ≤ a).
    We conclude that (& b = -a <= -m).
Qed.


Lemma low_bd_set_opp_to_upp_bd_set :
  ∀ (A : ℝ → Prop) (m : ℝ),
    is_lower_bound (set_opp A) m ⇒ 
      -m is an upper bound for A.
Proof.
    Take A : (ℝ → Prop) and m : ℝ.
    Assume that (is_lower_bound (set_opp A) m).
    We need to show that (∀ a : ℝ, (A a) ⇒ a ≤ -m).
    Take a : ℝ. Assume that (A a).
    It holds that (for all b : ℝ, (set_opp A b) ⇒ m ≤ b).
    We claim that (A (--a)).
    { It holds that (--a = a) (ii).
      It holds that (A a) (iii).
      (* TODO: We conclude that (--a ∈ A). should work *)
      exact (eq_ind_r(_,_,A,(iii),_,(ii))).
    }
    It holds that ((set_opp A) (-a)).
    Define b := (-a).
    It holds that (m ≤ b).
    It holds that (m ≤ -a).
    We conclude that (a ≤ - m).
Qed.


Lemma upp_bd_set_opp_to_low_bd_set :
  ∀ (A : ℝ → Prop) (M : ℝ),
    is_upper_bound (set_opp A) M ⇒
      is_lower_bound A (-M).
Proof.
    Take A : (ℝ → Prop) and M : ℝ.
    Assume that (is_upper_bound (set_opp A) M) (i).
    We need to show that (∀ a : ℝ, (A a) ⇒ -M ≤ a).
    Take a : ℝ. Assume that (A a).
    We claim that (A (--a)).
    { It holds that (--a = a) (ii).
      It holds that (A a) (iii).
      (* TODO: We conclude that (--a ∈ A). should work *)
      exact (eq_ind_r(_,_,A,(iii),_,(ii))).
    }
    It holds that ((set_opp A) (-a)).
    Define b := (-a).
    By (i) it holds that (b ≤ M).
    It holds that (-a ≤ M).
    We conclude that (- M ≤ a).
Qed.

Lemma bdd_below_to_bdd_above_set_opp :
  ∀ (A : ℝ → Prop),
    is_bounded_below A ⇒ is_bounded_above (set_opp A).
Proof.
    Take A : (ℝ → Prop).
    Assume that (is_bounded_below A) (i).
    We need to show that (∃ M : ℝ, is_upper_bound (set_opp A) M).
    By (i) it holds that (there exists m : ℝ, is_lower_bound A m).
    Obtain such an m.
    Choose M := (-m).
    By low_bd_set_to_upp_bd_set_opp we conclude that (is_upper_bound (set_opp A) (M)).
Qed.


Lemma sup_set_opp_is_inf_set :
  ∀ (A : ℝ → Prop) (M : ℝ),
    is_sup (set_opp A) M ⇒ is_inf A (-M).
Proof.
    Take A : (ℝ → Prop) and M : ℝ.
    Assume that (is_sup (set_opp A) M).
    It holds that (is_upper_bound (set_opp A) M 
        ∧ (for all M0 : ℝ, is_upper_bound (set_opp A) M0 ⇨ M ≤ M0)) (i).
    Because (i) both (is_upper_bound (set_opp A) M) and
      (for all M0 : ℝ, is_upper_bound (set_opp A) M0 ⇨ M ≤ M0) hold.
    We need to show that
      (is_lower_bound A (- M) ∧ (for all l : ℝ, is_lower_bound A l ⇨ l ≤ -M)).
    We show both statements.
    - We need to show that (is_lower_bound A (- M)).
      We claim that (is_upper_bound (set_opp A) M).
      We need to show that (for all a : ℝ, (set_opp A a) ⇒ a ≤ M).
      Take a : ℝ. Assume that (set_opp A a).
      It holds that (for all x : ℝ, (set_opp A x) ⇒ x ≤ M) (ii).
      By (ii) it holds that (is_upper_bound (set_opp A) M).
      We conclude that (a <= M).

      By upp_bd_set_opp_to_low_bd_set we conclude that (is_lower_bound A (-M)).

    - We need to show that (∀ l : ℝ, is_lower_bound A l ⇒ l ≤ -M).
      Take l : ℝ.
      Assume that (is_lower_bound A l).
      It holds that (is_upper_bound (set_opp A) M 
        ∧ (for all M0 : ℝ, is_upper_bound (set_opp A) M0 ⇨ M ≤ M0)).
      It holds that (∀ b : ℝ, is_upper_bound (set_opp A) b ⇒ M ≤ b) (ii).
      By low_bd_set_to_upp_bd_set_opp it holds that (is_upper_bound (set_opp A) (-l)).
      By (ii) it holds that (M ≤ -l).
      We conclude that (l ≤ - M).
Qed.

Lemma exists_inf :
  ∀ (A : ℝ → Prop) (x : ℝ), (A x) ⇒ is_bounded_below A ⇒
    exists (m : ℝ), is_inf A m.
Proof.
    Take A : (ℝ → Prop).
    Take z : ℝ. Assume that (A z).
    Assume that (is_bounded_below A) (vi).
    Define B := (set_opp A).
    We claim that (is_bounded_above B) (i).
    { By bdd_below_to_bdd_above_set_opp it suffices to show that (is_bounded_below A).
      We conclude that (is_bounded_below A).
    }
    We claim that (A (--z)).
    { It holds that (--z = z) (ii).
      It holds that (A z) (iii).
      (* TODO: We conclude that (--z ∈ A). should work *)
      exact (eq_ind_r(_,_,A,(iii),_,(ii))).
    }
    It holds that ((set_opp A) (-z)) (iv).
    It holds that (B (-z)).    
    By R_complete it holds that (there exists M : ℝ, is_sup B M).
    Obtain such an M.
    Choose m := (- M).
    By sup_set_opp_is_inf_set we conclude that (is_inf A m).
Qed.

(** ### A supremum is an upper bound

If $M$ is the supremum of a set $A$, it is also an upper bound.*)
Lemma sup_is_upp_bd :
  ∀ A : (ℝ → Prop),
    ∀ M : ℝ,
      is_sup A M ⇒ is_upper_bound A M.
Proof.
    Take A : (ℝ → Prop).
    Take M : ℝ.
    Assume that (is_sup A M).
    It holds that (is_upper_bound A M 
      ∧ (for all b : ℝ, is_upper_bound A b ⇨ M ≤ b)) (i).
    Because (i) both (is_upper_bound A M) and
      (for all M0 : ℝ, is_upper_bound A M0 ⇨ M ≤ M0) hold.
    It follows that (is_upper_bound A M).
Qed.

(** ### Any upper bound is greater than or equal to the supremum*)
Lemma any_upp_bd_ge_sup :
  ∀ A : (ℝ → Prop),
    ∀ M L : ℝ,
      is_sup A M ⇒ (is_upper_bound A L ⇒ M ≤ L).
Proof.
    Take A : (ℝ → Prop).
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
  ∀ A : (ℝ → Prop),
    ∀ m : ℝ,
      is_inf A m ⇒ is_lower_bound A m.
Proof.
    Take A : (ℝ → Prop).
    Take m : R.
    Assume that (is_inf A m) (i).
    Because (i) both (is_lower_bound A m) (ii) and
      (for all M0 : ℝ, is_lower_bound A M0 ⇨ M0 ≤ m) hold.
    By (ii) we conclude that (is_lower_bound A m).
Qed.
(** ## Any lower bound is less than or equal to the infimum*)
Lemma any_low_bd_le_inf :
  ∀ A : (ℝ → Prop),
    ∀ m l : ℝ,
      is_inf A m ⇒ is_lower_bound A l ⇒ l ≤ m.
Proof.
    Take A : (ℝ → Prop).
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
  ∀ (A : ℝ → Prop) (M : ℝ),
    is_sup A M ⇒
      ∀ (L : ℝ), L < M ⇒ 
        ∃ a : ℝ, (A a) ∧ L < a.
Proof.
    Take A : (ℝ → Prop).
    Take M : ℝ.
    Assume that (is_sup A M).
    Take L : ℝ.
    Assume that (L < M).
    We argue by contradiction.
    Assume that (¬ (there exists a : ℝ, (A a) ∧ L < a)) (i). 
    It holds that (∀ x : ℝ, (A x) ⇒ x <= L) (ii).
    By (ii) it holds that (is_upper_bound A L).
    (** TODO: why can't this be done automatically? *)
    By any_upp_bd_ge_sup it holds that (M <= L).
    It holds that (¬(M ≤ L)).
    Contradiction.
Qed.

Lemma exists_almost_minimizer :
  ∀ (A : ℝ → Prop) (m : ℝ),
    is_inf A m ⇒
      ∀ (L : ℝ), L > m ⇒ 
        ∃ a : ℝ, (A a) ∧ L > a.
Proof.
    Take A : (ℝ → Prop).
    Take m : ℝ.
    Assume that (is_inf A m).
    Take L : ℝ.
    Assume that (L > m).
    We argue by contradiction.
    Assume that (¬ (there exists a : ℝ, (A a) ∧ L > a)).
    It holds that (∀ x : ℝ, (A x) ⇒ L ≤ x) (i).
    By (i) it holds that (is_lower_bound A L).
    (** TODO: why can't this be done automatically? *)
    By any_low_bd_le_inf it holds that (L <= m).
    It holds that (¬(L ≤ m)).
    Contradiction.
Qed.

Lemma if_almost_maximizer_then_every_upp_bd_larger :
  ∀ (A : ℝ → Prop) (M : ℝ),
    (∀ (L : ℝ), L < M ⇒ ∃ a : ℝ, (A a) ∧ L < a)
       ⇒ ∀ (K : ℝ), is_upper_bound A K ⇒ M ≤ K.
Proof.
Take A : (ℝ → Prop) and M : ℝ.
Assume that (∀ L : ℝ, L < M ⇒ there exists a : ℝ, (A a) ∧ L < a) (i).
Take K : ℝ.
Assume that (is_upper_bound A K).
It holds that (∀ a : ℝ, (A a) ⇒ a ≤ K) (ii).
We need to show that (M ≤ K).
We argue by contradiction.
Assume that (¬ M ≤ K).
It holds that (M > K).
By (i) it holds that (∃ a : ℝ, (A a) ∧ K < a).
Obtain such an a. It holds that ((A a) ∧ (K < a)) (iii).
Because (iii) both (A a) and (K < a) hold.
By (ii) it holds that (a ≤ K).
It holds that (K < K).
It holds that (¬ (K < K)).
Contradiction.
Qed.

Lemma if_almost_minimizer_then_every_low_bd_smaller :
  ∀ (A : ℝ → Prop) (m : ℝ),
    (∀ (L : ℝ), L > m ⇒ ∃ a : ℝ, (A a) ∧ L > a)
       ⇒ ∀ (K : ℝ), is_lower_bound A K ⇒ K ≤ m.
Proof.
Take A : (ℝ → Prop) and m : ℝ.
Assume that (∀ L : ℝ, L > m ⇒ there exists a : ℝ, (A a) ∧ L > a) (i).
Take K : ℝ.
Assume that (is_lower_bound A K).
It holds that (∀ a : ℝ, (A a) ⇒ K ≤ a) (ii).
We need to show that (K ≤ m).
We argue by contradiction.
Assume that (¬ K ≤ m).
It holds that (K > m).
By (i) it holds that (∃ a : ℝ, (A a) ∧ K > a).
Obtain such an a. It holds that ((A a) ∧ (K > a)) (iii).
Because (iii) both (A a) and (K > a) hold.
By (ii) it holds that (K ≤ a).
It holds that (K > K).
It holds that (¬ (K > K)).
Contradiction.
Qed.

Lemma if_almost_maximizer_ε_then_every_upp_bd_larger :
  ∀ (A : ℝ → Prop) (M : ℝ),
    (∀ (ε : ℝ), ε > 0 ⇒ ∃ a : ℝ, (A a) ∧ M - ε < a)
       ⇒ ∀ (K : ℝ), is_upper_bound A K ⇒ M ≤ K.
Proof.
  Take A : (ℝ → Prop) and M : ℝ.
  Assume that (for all ε : ℝ, ε > 0 ⇨ there exists a : ℝ, (A a) ∧ M - ε < a) (i).
  apply if_almost_maximizer_then_every_upp_bd_larger.
  Take L : ℝ; such that (L < M).
  It holds that (M - L > 0).
  Define ε1 := (M - L).
  It holds that (ε1 > 0).
  By (i) it holds that (there exists a : ℝ, (A a) ∧ M - ε1 < a).
  Obtain such an a. It holds that ((A a) ∧ (M - ε1 < a)) (ii).
  Because (ii) both (A a) and (M - ε1 < a) hold.
  Choose (a).
  We show both (A a) and (L < a).
  - We conclude that (A a).
  - We conclude that (& L = M - (M - L) = M - ε1 < a).
Qed.

Lemma if_almost_minimizer_ε_then_every_low_bd_smaller :
  ∀ (A : ℝ → Prop) (m : ℝ),
    (∀ (ε : ℝ), ε > 0 ⇒ ∃ a : ℝ, (A a) ∧ m + ε > a)
       ⇒ ∀ (K : ℝ), is_lower_bound A K ⇒ K ≤ m.
Proof.
  Take A : (ℝ → Prop) and m : ℝ.
  Assume that (for all ε : ℝ, ε > 0 ⇨ there exists a : ℝ, (A a) ∧ m + ε > a) (i).
  apply if_almost_minimizer_then_every_low_bd_smaller.
  Take L : ℝ; such that (L > m).
  It holds that (L - m > 0).
  Define ε1 := (L - m).
  It holds that (ε1 > 0).
  By (i) it holds that (there exists a : ℝ, (A a) ∧ m + ε1 > a).
  Obtain such an a. It holds that ((A a) ∧ (m + ε1 > a)) (ii).
  Choose (a).
  Because (ii) both (A a) and (m + ε1 > a) hold.
  We show both (A a) and (L > a).
  - We conclude that (A a).
  - We conclude that (& a < m + ε1 = m + L - m = L).
Qed.

Lemma exists_almost_maximizer_ε :
  ∀ (A : ℝ → Prop) (M : ℝ),
    is_sup A M ⇒
      ∀ (ε : ℝ), ε > 0 ⇒ 
        ∃ a : R, (A a) ∧ M - ε < a.
Proof.
    Take A : (ℝ → Prop).
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
  ∀ (A : ℝ → Prop) (m : ℝ),
    is_inf A m ⇒
      ∀ (ε : ℝ), ε > 0 ⇒ 
        ∃ a : ℝ, (A a) ∧ m + ε > a.
Proof.
    Take A : (ℝ → Prop).
    Take m : ℝ.
    Assume that (is_inf A m).
    Take ε : ℝ; such that (ε > 0).
    It holds that (m + ε > m).
    (** TODO: fix this *)
    apply exists_almost_minimizer with (L := m + ε) (m := m).
    - We conclude that (is_inf A m).
    - We conclude that (m + ε > m).
Qed.

Definition is_sup_alt_char (A : ℝ → Prop) (M : ℝ):=
  is_upper_bound A M ∧ (∀ (ε : ℝ), ε > 0 ⇒ 
        ∃ a : ℝ, (A a) ∧ M - ε < a).

Definition is_inf_alt_char (A : ℝ → Prop) (m : ℝ):=
  is_lower_bound A m ∧ (∀ (ε : ℝ), ε > 0 ⇒ 
        ∃ a : ℝ, (A a) ∧ m +  ε > a).

Theorem alt_char_sup :
  ∀ (A : ℝ → Prop) (M : ℝ),
    is_sup A M ⇔ is_sup_alt_char A M.
Proof.
  Take A : (ℝ → Prop) and M : ℝ.
  We show both directions.
  - We need to show that (is_sup A M ⇨ is_sup_alt_char A M).
    Assume that (is_sup A M).
    We need to show that (
    is_upper_bound A M
    ∧ (for all ε : ℝ,
      ε > 0 ⇨ there exists a : ℝ, (A a) ∧
                M - ε < a) ).
    We show both statements.
    + We need to show that (is_upper_bound A M).
      It holds that (
      is_upper_bound A M
      ∧ (for all M0 : ℝ,
        is_upper_bound A M0 ⇨ M ≤ M0) ) (i).
      Because (i) both (is_upper_bound A M) and
        (for all M0 : ℝ, is_upper_bound A M0 ⇨ M ≤ M0) hold.
      It follows that (is_upper_bound A M).

    + We need to show that (for all ε : ℝ, ε > 0 ⇨ there exists a : ℝ, (A a) ∧ M - ε < a ).
      apply exists_almost_maximizer_ε.
      We conclude that (M is the supremum of A).

  - We need to show that (is_sup_alt_char A M ⇨ is_sup A M).
    Assume that (is_sup_alt_char A M).
    It holds that (
    is_upper_bound A M
    ∧ (for all ε : ℝ,
      ε > 0 ⇨ there exists a : ℝ, (A a) ∧
                M - ε < a) ) (i).
    Because (i) both (is_upper_bound A M) (ii) and
      (for all ε : ℝ, ε > 0 ⇨ there exists a : ℝ, (A a) ∧ M - ε < a) (iii) hold.

    We need to show that (
    is_upper_bound A M
    ∧ (for all M0 : ℝ,
      is_upper_bound A M0 ⇨ M ≤ M0) ).
    We show both statements.
    + We need to show that (is_upper_bound A M).
      By (ii) we conclude that (is_upper_bound A M).
    + We need to show that (for all M0 : ℝ, is_upper_bound A M0 ⇨ M ≤ M0).
      apply if_almost_maximizer_ε_then_every_upp_bd_larger.
      By (iii) we conclude that (for all ε : ℝ,
      ε > 0 ⇨ there exists a : ℝ,
                A(a) ∧ M - ε < a).
Qed.

Theorem alt_char_inf :
  ∀ (A : ℝ → Prop) (m : ℝ),
    is_inf A m ⇔ is_inf_alt_char A m.
Proof.
  Take A : (ℝ → Prop) and m : ℝ.
  We show both directions.
  - We need to show that (is_inf A m ⇨ is_inf_alt_char A m).
    Assume that (is_inf A m).
    We need to show that (
    is_lower_bound A m
    ∧ (for all ε : ℝ,
      ε > 0 ⇨ there exists a : ℝ, (A a) ∧
                m + ε > a) ).
    We show both statements.
    + We need to show that (is_lower_bound A m).
      It holds that (
      is_lower_bound A m ∧ (for all l : ℝ,
                          is_lower_bound A l ⇨ l ≤ m) 
      ) (i).
      Because (i) both (is_lower_bound A m) and
        (for all l : ℝ, is_lower_bound A l ⇨ l ≤ m) hold.
      It follows that (is_lower_bound A m).

    + We need to show that (for all ε : ℝ, ε > 0 ⇨ there exists a : ℝ, (A a) ∧ m + ε > a).
        
      By exists_almost_minimizer_ε we conclude that
      (for all ε : ℝ,
        ε > 0 ⇨ there exists a : ℝ, (A a) ∧
              m + ε > a).

  - We need to show that (is_inf_alt_char A m ⇨ is_inf A m).
    Assume that (is_inf_alt_char A m).
    It holds that (
      is_lower_bound A m
      ∧ (for all ε : ℝ,
      ε > 0 ⇨ there exists a : ℝ, (A a) ∧
                m + ε > a) ) (i).
    Because (i) both (is_lower_bound A m) (ii) and
      (for all ε : ℝ, ε > 0 ⇨ there exists a : ℝ, (A a) ∧ m + ε > a) hold.

    We need to show that (
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
  ∀ (A : ℝ → Prop) (M : ℝ),
    is_sup A M ⇒ 
      (A M) ∨ (∀ a : ℝ, (A a) ⇒ a < M).
Proof.
    Take A : (ℝ → Prop).
    Take M : ℝ.
    Assume that (is_sup A M).
    We argue by contradiction.
    Assume that (¬ (A M ∨ (for all a : ℝ, (A a) ⇒ a < M))).
    It holds that ((¬ (A M)) ∧ 
      ¬(∀ a : ℝ, (A a) ⇒ a < M)) (i).
    Because (i) both(¬ (A M)) and (¬(∀ a : ℝ, (A a) ⇒ a < M)) hold.
    We claim that (for all a : ℝ, (A a) ⇒ a < M).
    { 
      Take a : ℝ. Assume that (A a).
      By sup_is_upp_bd it holds that (is_upper_bound A M).
      It holds that (a ≤ M).
      We claim that (M ≠ a).
      {
        Assume that (M = a) (ii).
        We claim that (A M).
        { It holds that (A a) (iii).
          (* TODO: We conclude that (A M). should work *)
      exact (eq_ind_r(_,_,A,(iii),_,(ii))).
        }
        Contradiction.
      }
      We conclude that (a < M).
    }
    Contradiction.
Qed.

(** * Lemmas for convenience*)
Lemma bounded_by_upper_bound_propform :
  ∀ (A : ℝ → Prop) (M : ℝ) (b : ℝ),
    is_upper_bound A M ⇒ A b ⇒ b ≤ M.
Proof.
    Take A : (ℝ → Prop).
    Take M : ℝ.
    Take b : ℝ.
    Assume that (is_upper_bound A M) (i).
    Assume that (A b) (ii).
    We conclude that (b ≤ M).
Qed.

Lemma bounded_by_lower_bound_propform :
  ∀ (A : ℝ → Prop) (m : ℝ) (b : ℝ),
    is_lower_bound A m ⇒ A b ⇒ m ≤ b.
Proof.
    Take A : (ℝ → Prop).
    Take m : ℝ.
    Take b: ℝ.
    Assume that (is_lower_bound A m) (i).
    Assume that (A b) (ii).
    We conclude that (m ≤ b).
Qed.

Lemma seq_ex_almost_maximizer_ε :
  ∀ (a : ℕ → ℝ) (pr : has_ub a) (ε : ℝ), 
    ε > 0 ⇒ ∃ k : ℕ, a k > lub a pr - ε.
Proof.
    Take a : (ℕ → ℝ).
    Assume that (has_ub a) (i).
    We need to show that (for all ε : ℝ,  ε > 0 
      ⇨ there exists k : ℕ, a k > (let (a0, _) := ub_to_lub a (i) in a0) - ε).
    Define lub_a_prf := (ub_to_lub a (i)).
    clear _defeq. Obtain such an l.
    Take ε : ℝ; such that (ε > 0).
    By exists_almost_maximizer_ε it holds that (∃ y : ℝ, (EUn a) y ∧ y > l - ε).
    Obtain such a y. It holds that ((EUn a) y ∧ y > l - ε) (iv).
    Because (iv) both (EUn a y) and (y > l - ε) hold.
    It holds that (there exists n : ℕ , y = a n).
    Obtain such an n.
    Choose k := n.
    We need to show that (l - ε < a n).
    We conclude that (& l - ε < y = a n).
Qed.

Lemma seq_ex_almost_maximizer_m :
  ∀ (a : ℕ → ℝ) (pr : has_ub a) (m : ℕ), 
    ∃ k : ℕ, a k > lub a pr - 1 / (INR(m) + 1).
Proof.
    Take a : (ℕ → ℝ).
    Assume that (has_ub a).
    Take m : ℕ.
    apply seq_ex_almost_maximizer_ε.
    (** We need to show that $1/(m+1) > 0$.*)
    It holds that (0 < m + 1)%R.
    We conclude that (1 / (m+1) > 0).
Qed.

Lemma exists_almost_lim_sup_aux :
  ∀ (a : ℕ → ℝ) (pr : has_ub a) (m : ℕ) (N : ℕ),
    ∃ k : ℕ, (k ≥ N)%nat ∧ a k > sequence_ub a pr N - 1 / (INR(m) + 1).
Proof.
    Take a : (ℕ → ℝ).
    Assume that (has_ub a) (i).
    Take m, Nn : ℕ.
    By seq_ex_almost_maximizer_m it holds that
      (∃ k : ℕ, a (Nn + k)%nat > sequence_ub a (i) Nn - 1 / (INR m + 1)).
    Obtain such a k. Choose l := (Nn+k)%nat.
    We show both statements.
    - We need to show that (l ≥ Nn)%nat.
      We conclude that (l ≥ Nn)%nat.
    - We need to show that ( a l > sequence_ub a (i) Nn - 1 / (m + 1) ).
      We conclude that ( a l > sequence_ub a (i) Nn - 1 / (m + 1) ).
Qed.

#[export] Hint Resolve bounded_by_upper_bound_propform : wp_reals.
#[export] Hint Resolve bounded_by_lower_bound_propform : wp_reals.
#[export] Hint Resolve alt_char_inf : wp_reals.
#[export] Hint Resolve alt_char_sup : wp_reals.
#[export] Hint Resolve <- alt_char_inf : wp_reals.
#[export] Hint Resolve <- alt_char_sup : wp_reals.

(** ### **Hints***)
#[export] Hint Unfold is_lub : wp_reals.
#[export] Hint Unfold is_inf : wp_reals.
#[export] Hint Unfold is_upper_bound : wp_reals.
#[export] Hint Unfold is_lower_bound :reals.

Close Scope R_scope.