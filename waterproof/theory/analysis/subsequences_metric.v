(** * [subsequences_definitions.v.v]
Authors:
    - Jim Portegies
    - Lulof Pirée (minor edits)
    - Cosmin Manea (minor edits)
Creation date: 17 June 2021

--------------------------------------------------------------------------------

This file is part of Waterproof-lib.

Waterproof-lib is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

Waterproof-lib is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.    See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with Waterproof-lib.    If not, see <https://www.gnu.org/licenses/>.
*)

(** ## Subsequences definitions*)
Require Import Reals.
Require Import Waterproof.notations.notations.
Require Import Waterproof.AllTactics.
Require Import Waterproof.load_database.RealsAndIntegers.
Require Import Waterproof.set_search_depth.To_5.
Require Import Waterproof.set_intuition.Disabled.
Require Import Waterproof.theory.analysis.metric_spaces.
Require Import Waterproof.theory.analysis.sequences_metric.

Open Scope metric_scope.
Definition is_index_sequence    (n : ℕ → ℕ) := 
    ∀ k : ℕ,
        (n k < n (k + 1))%nat.


(** The next definition captures what it means to be an index sequence.*)
Definition is_index_seq (n : ℕ → ℕ) :=
    ∀ k : ℕ, (n k < n (S k))%nat.
    
Variable M : Metric_Space.
Definition X := Base M.
Definition dist := dist M.

Notation "a ◦ n" := (fun (k : nat) => a (n k)) (right associativity, at level 20).
Notation "a ◦ n ◦ m" := (fun (k : nat) => a (n (m k))) (right associativity, at level 21).

Definition is_subsequence (b : ℕ → X) (a : ℕ → X) := 
    ∃ m : (ℕ → ℕ),
        is_index_sequence m ∧ ∀ k : ℕ,
            b k = (a ◦ m) k.

Definition is_accumulation_point (p : X) (a : ℕ → X) :=
    ∃ l : (ℕ → ℕ),
        is_index_sequence l ∧ (a ◦ l) ⟶ p.



Lemma index_sequence_property (n : ℕ → ℕ) :
    is_index_sequence n ⇒ 
        ∀ k : ℕ,
            (n k ≥ k)%nat.
Proof.
    intros. 
    unfold is_index_sequence in H.
    induction k.
    specialize (H 0%nat). 
    unfold ge.
    apply Nat.le_0_l.
    specialize (H k). 
    unfold ge. 
    apply lt_le_S. 
    rewrite Nat.add_1_r in H.
    apply (Nat.le_lt_trans k (n k)). 
    apply IHk. 
    apply H.
Qed.

Global Hint Resolve index_sequence_property : subsequences.
Global Hint Extern 1 => (unfold ge) : subsequences.



Require Import Arith.


Lemma successor_is_plus_one: forall k: nat, (k + 1)%nat = S k.
    This follows immediately.
Qed.


Lemma index_seq_equiv (n : ℕ → ℕ) : is_index_seq n ⇔ is_index_sequence n.
Proof. 
    We show both directions.
    - We need to show that (is_index_seq n ⇨ is_index_sequence n).
      intro.
      unfold is_index_sequence. 
      Take k : ℕ. 
      unfold is_index_seq in H. 
      rewrite successor_is_plus_one.
      Apply H.
    - We need to show that (is_index_sequence n ⇨ is_index_seq n).
      intro.
      unfold is_index_seq. 
      Take k : ℕ. 
      unfold is_index_sequence in H. 
      rewrite <- successor_is_plus_one.
      Apply H.
Qed.



Definition is_increasing (g : ℕ → ℕ) :=
  ∀ k : ℕ, (g k ≤ g (S k))%nat.

Lemma incr_loc_to_glob :
  ∀ g : ℕ → ℕ,
    is_increasing g
      ⇒ (∀ k l : ℕ, (k ≤ l)%nat ⇒ (g k ≤ g l)%nat).
Proof.
    (* There exists already a constant called [f].*) 
    Take g : (ℕ → ℕ).
    Expand the definition of is_increasing. (*TODO: the layout of is_increasing is confusing*)
    That is, write the goal as 
      ((for all k : ℕ, (g k ≤ g (S k))%nat) ⇨ for all k l : ℕ, (k ≤ l ⇨ g k ≤ g l)%nat ).
    Check family.
    Locate family.
    Check ℕ.
    Assume incr_loc : (∀ k : ℕ, ((g k) ≤ (g (S k)))%nat).
    Take k : ℕ.
    induction l as [|l IH_l]. 
    (** We first need to show that if $k \leq 0$ then $(f (k) \leq f(0))$.*)
    Assume k_le_0 : ((k ≤ 0)%nat). 
    Rewrite using (k = 0)%nat. 
    We need to show that (g 0 ≤ g 0)%nat.
    This follows immediately.
    (** Next, we need to show that if $k \leq S (l)$ then $f(k) \leq f(S (l))$.*)
    Assume Sk_le_Sl : ((k ≤ S l)%nat).
    destruct (lt_eq_lt_dec k (S l)) as [temp | k_gt_Sl].
    destruct temp as [k_lt_Sl | k_eq_Sl].
    (** We first consider the case that $k < S(l)$.*)
    It holds that k_le_l: (k ≤ l)%nat.
    By IH_l it holds that gk_le_gl : (g k ≤ g l)%nat.
    It holds that gl_le_g_Sl: (g l ≤ g (S l))%nat.

    apply le_trans with (n := (g k)) (m := g l) (p := g (S l)).
    exact gk_le_gl.
    exact gl_le_g_Sl.
    (** We now consider the case $k = S(l)$. We need to show that $f(k) \leq f(S(l))$. *)
    Rewrite using (k = S l).
    This follows by reflexivity.
    (** Finally we consider the case $k > S(l)$. However, this case is in contradiction with $k \leq S(l)$. *)
    It holds that not_Sl_lt_k: (¬(S l < k)%nat). 
    Contradiction.
Qed.


Lemma index_sequence_property2 (n : ℕ → ℕ) : 
    is_index_sequence n ⇒ 
        ∀ k1 k2 : ℕ, 
            (k1 ≥ k2)%nat ⇒ 
                (n k1 ≥ n k2)%nat.
Proof.
    Assume H : (is_index_sequence n).
    Take k1, k2 : ℕ.
    Assume k1_ge_k2 : (k1 ≥ k2)%nat.
    We need to show that (n k1 ≥ n k2)%nat.

    ltac1:(pose proof (incr_loc_to_glob n)).
    We claim that n_is_increasing : (is_increasing n).
    Expand the definition of is_increasing.
    That is, write the goal as (for all k : ℕ, (n k ≤ n (S k))%nat).
    Take k : ℕ.
    It holds that temp : (n k ≤ n (k+1))%nat.
    It holds that temp2 : (k+1 = S k)%nat.
    Write goal using (S k = (k + 1)%nat) as ((n k ≤ n (k + 1))%nat).
    Apply temp.
    Apply H0. 
    Apply n_is_increasing. 
    Apply k1_ge_k2.
Qed.

Global Hint Resolve index_sequence_property2 : subsequences.


Lemma double_is_even : forall n : nat, Nat.even (2 * n) = true.
Proof.
    Take n : nat.
    Rewrite equality (Nat.even (2*n)) "=" (Nat.even (0 + 2 * n)).
    rewrite Nat.even_add_mul_2.
    This concludes the proof.
Qed.

Global Hint Resolve double_is_even : subsequences.

Lemma subsequence_of_convergent_sequence : ∀ a : (ℕ → X), ∀ p : X, a ⟶ p ⇒ ∀ (n : ℕ → ℕ), is_index_sequence n ⇒ (a ◦ n) ⟶ p.
Proof.
Take a : (ℕ → X), p : X.
Assume a_converges_to_p : (a ⟶ p).
Take n : (ℕ → ℕ).
Assume n_is_index_sequence : (is_index_sequence n).
It suffices to show that (∀ ε : ℝ, ε > 0 ⇒ ∃ N3 : ℕ, ∀ k : ℕ, (k ≥ N3)%nat ⇒ dist (a (n k)) p < ε).

Take ε : ℝ. Assume ε_pos : (ε > 0).
Choose K such that k_le_K_a_k_to_p according to (a_converges_to_p ε ε_pos).
Choose N3 := K.
Take k : ℕ. Assume k_ge_N : (k ≥ N3)%nat.
By index_sequence_property2 it holds that H : (n k ≥ n K)%nat.
By index_sequence_property it holds that H2 : (n K ≥ K)%nat.
assert (H3 : (n k ≥ K)%nat) by auto with zarith.
We conclude that (dist (a (n k)) p < ε).
Qed.

Lemma equivalent_subsequence_convergence : 
  ∀ (x y : ℕ → X), is_subsequence y x ⇒ 
    ∀ p : X, x ⟶ p ⇒
      y ⟶ p.
Proof.
Take x, y : (ℕ → X).
Assume y_subsequence_of_x : (is_subsequence y x).
Take p : X.
Assume x_converges_to_p : (x ⟶ p).

We need to show that (y ⟶ p).
It holds that y_sub_x : (∃ m : ℕ → ℕ, is_index_sequence m ∧ ∀ k : ℕ, y k = (x ◦ m) k).
Choose m such that m_is_index_and_y_eq_x_m according to y_sub_x.
Because m_is_index_and_y_eq_x_m both m_is_index and y_eq_x_m.

It suffices to show that (∀ ε : ℝ, ε > 0 ⇒ ∃ N3 : ℕ, ∀ k : ℕ, (k ≥ N3)%nat ⇒ dist (y k) p < ε).

Take ε : ℝ. Assume ε_pos : (ε > 0).
Choose K such that k_le_K_x_k_to_p according to (x_converges_to_p ε ε_pos).
Choose N3 := K.
Take k : ℕ. Assume k_ge_N : (k ≥ N3)%nat.
It holds that y_k_eq_x_m_k : (y k = x (m k)).
Write goal using (y k = x (m k)) as (dist (x (m k)) p < ε).

By index_sequence_property2 it holds that H : (m k ≥ m K)%nat.
By index_sequence_property it holds that H2 : (m K ≥ K)%nat.
assert (H3 : (m k ≥ K)%nat ) by auto with zarith.
We conclude that (dist (x (m k)) p < ε).
Qed.
