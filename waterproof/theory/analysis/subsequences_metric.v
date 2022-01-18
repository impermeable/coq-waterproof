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
    ∀ k : ℕ, (n k < n (k + 1))%nat.
    
Variable M : Metric_Space.
Definition X := Base M.
Definition dist := dist M.

Notation "a ◦ n" := (fun (k : nat) => a (n k)) (right associativity, at level 11).
Notation "a ◦ n ◦ m" := (fun (k : nat) => a (n (m k))) (right associativity, at level 12).

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

Lemma index_seq_equiv (n : ℕ → ℕ) : is_index_seq n ⇔ is_index_sequence n.
Proof. 
    We show both directions.
    - We need to show that (is_index_seq n ⇨ is_index_sequence n).
      intro.
      unfold is_index_sequence. 
      Take k : ℕ. 
      unfold is_index_seq in H.
      We conclude that ((n k < n (k + 1))%nat).
    - We need to show that (is_index_sequence n ⇨ is_index_seq n).
      intro.
      unfold is_index_seq. 
      Take k : ℕ. 
      unfold is_index_sequence in H.
      We conclude that ((n k < n (k + 1))%nat).
Qed.



Definition is_increasing (g : ℕ → ℕ) :=
  ∀ k : ℕ, (g k ≤ g (k + 1))%nat.

Lemma incr_loc_to_glob :
  ∀ g : ℕ → ℕ,
    is_increasing g
      ⇒ (∀ k l : ℕ, (k ≤ l)%nat ⇒ (g k ≤ g l)%nat).
Proof.
    (* There exists already a constant called [f].*) 
    Take g : (ℕ → ℕ).
    Expand the definition of is_increasing. (*TODO: the layout of is_increasing is confusing*)
    That is, write the goal as 
      ((for all k : ℕ, (g k ≤ g (k + 1))%nat) ⇨ for all k l : ℕ, (k ≤ l ⇨ g k ≤ g l)%nat ).
    Check family.
    Locate family.
    Check ℕ.
    Assume (∀ k : ℕ, (g k) ≤ (g (k + 1)))%nat.
    Take k : ℕ.
    We use induction on l.
    - We first show the base case, namely ((k ≤ 0)%nat ⇨ (g k ≤ g 0)%nat).
      Assume (k ≤ 0)%nat.
      It holds that (k = 0)%nat.
      It suffices to show that (g k = g 0)%nat.
      We conclude that (g k = g 0)%nat.
    - We now show the induction step.
      Assume ((k ≤ l) ⇨ (g k ≤ g l))%nat (IH).
      Assume (k ≤ l + 1)%nat.
      destruct (lt_eq_lt_dec k (l + 1)) as [[k_lt_Sl | k_eq_Sl] | k_gt_Sl].
      + (** We first consider the case that $k < l + 1$.*)
        It holds that (k ≤ l)%nat.
        We conclude that (& g k &<= g l &<= g (l + 1))%nat.
      + (** We now consider the case $k = S(l)$. We need to show that $f(k) \leq f(S(l))$. *)
        It suffices to show that (g k = g (l + 1))%nat.
        We conclude that (g k = g (l + 1))%nat.
      + (** Finally we consider the case $k > S(l)$. However, this case is in contradiction with $k \leq S(l)$. *)
        It holds that (¬(l + 1 < k)%nat). 
        Contradiction.
Qed.


Lemma index_sequence_property2 (n : ℕ → ℕ) : 
    is_index_sequence n ⇒ 
        ∀ k1 k2 : ℕ, 
            (k1 ≥ k2)%nat ⇒ 
                (n k1 ≥ n k2)%nat.
Proof.
    Assume (is_index_sequence n).
    Take k1, k2 : ℕ; such that (k1 ≥ k2)%nat.
    We need to show that (n k1 ≥ n k2)%nat.
    By incr_loc_to_glob it suffices to show that (is_increasing n).
    Expand the definition of is_increasing.
    That is, write the goal as (for all k : ℕ, (n k ≤ n (k + 1))%nat).
    Take k : ℕ.
    We conclude that (n k ≤ n (k+1))%nat.
Qed.

Global Hint Resolve index_sequence_property2 : subsequences.


Lemma double_is_even : forall n : nat, Nat.even (2 * n) = true.
Proof.
  Take n : nat.
  It holds that (Nat.even (2 * n) = Nat.even (0 + 2 * n)).
  It suffices to show that (Nat.even (0 + 2*n) = true).
  By Nat.even_add_mul_2 it holds that (Nat.even (0 + 2*n) = Nat.even 0).
  It holds that (Nat.even 0 = true).
  We conclude that (Nat.even (0 + 2 * n) = true).
Qed.

Global Hint Resolve double_is_even : subsequences.

Lemma subsequence_of_convergent_sequence : ∀ a : (ℕ → X), ∀ p : X, a ⟶ p ⇒ ∀ (n : ℕ → ℕ), is_index_sequence n ⇒ (a ◦ n) ⟶ p.
Proof.
Take a : (ℕ → X). Take p : X.
Assume (a ⟶ p).
Take n : (ℕ → ℕ).
Assume (is_index_sequence n).
It suffices to show that (∀ ε : ℝ, ε > 0 ⇒ ∃ N3 : ℕ, ∀ k : ℕ, (k ≥ N3)%nat ⇒ dist (a (n k)) p < ε).

Take ε : ℝ; such that (ε > 0).
It holds that (∃ N3 : ℕ, ∀ k : ℕ, (k ≥ N3)%nat → dist (a k) p < ε) (i).
Choose K such that (H1) according to (i).
Choose N3 := K.
Take k : ℕ; such that (k ≥ N3)%nat.
By index_sequence_property2 it holds that (n k ≥ n K)%nat.
By index_sequence_property it holds that (n K ≥ K)%nat.
assert (H3 : (n k ≥ K)%nat) by auto with zarith.
We conclude that (dist (a (n k)) p < ε).
Qed.

Lemma equivalent_subsequence_convergence : 
  ∀ (x y : ℕ → X), is_subsequence y x ⇒ 
    ∀ p : X, x ⟶ p ⇒
      y ⟶ p.
Proof.
Take x, y : (ℕ → X).
Assume (is_subsequence y x).
Take p : X.
Assume (x ⟶ p).

We need to show that (y ⟶ p).
It holds that (∃ m : ℕ → ℕ, is_index_sequence m ∧ ∀ k : ℕ, y k = (x ◦ m) k) (i).
Choose m such that (ii) according to (i).
Because (ii) both (is_index_sequence m) and 
  (for all k : nat, y k = x (m k)).

It suffices to show that (∀ ε : ℝ, ε > 0 ⇒ ∃ N3 : ℕ, ∀ k : ℕ, (k ≥ N3)%nat ⇒ dist (y k) p < ε).

Take ε : ℝ; such that (ε > 0).
It holds that (∃ N3 : ℕ, ∀ k : ℕ, (k ≥ N3)%nat → dist (x k) p < ε) (iii).
Choose K such that (H1) according to (iii).
Choose N3 := K.
Take k : ℕ; such that (k ≥ N3)%nat.
By index_sequence_property2 it holds that (m k ≥ m K)%nat.
By index_sequence_property it holds that (m K ≥ K)%nat.
It holds that (m k ≥ K)%nat.
It holds that (dist (x (m k)) p < ε).
It holds that (y k = x (m k)) (iv).
(* It holds that H5 : (dist (y k) p = dist (x (m k)) p). Why does this not work? *)
rewrite (iv).
We conclude that ( dist (x (m k)) p < ε).
Qed.
