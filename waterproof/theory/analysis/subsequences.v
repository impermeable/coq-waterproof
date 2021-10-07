(** * Subsequences

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
Require Import ZArith.
Require Import Lra.
Require Import Classical.
Require Import Classical_Pred_Type.
Require Import ClassicalChoice.

Require Import Waterproof.AllTactics.
Require Import Waterproof.contradiction_tactics.basic_contradiction.
Require Import Waterproof.load_database.All.
Require Import Waterproof.notations.notations.
Require Import Waterproof.set_search_depth.To_5.
Require Import Waterproof.set_intuition.Disabled.
Require Import Waterproof.load_database.DisableWildcard.

Global Hint Resolve Rabs_Rabsolu.
(** ## Creating a subsequence of elements satisfying a certain property

The purpose of this section is to provide a somewhat general strategy to construct subsequences of elements satisfying a certain property. *)
(** ### From existence of a next element to a function producing this element

The next lemma is quite technical, and is usually not so visible in classical analysis. We rely here on a version of the axiom of choice.*)
Lemma existence_next_el_to_fun :
    ∀ (a : ℕ → ℝ) (P : ℕ → ℝ → Prop),
    (∀ (m : ℕ) (N : ℕ), ∃ k : ℕ, (N ≤ k)%nat ∧ (P m (a k))) ⇒
      ∃ f : ℕ → ℕ → ℕ, ∀ (m : ℕ) (N : ℕ), (N ≤ f m N)%nat ∧ P m (a (f m N)).
Proof.
    Take a : (ℕ → ℝ). 
    Take P : (ℕ → ℝ → Prop).
    Assume ex_next : (for all m N : ℕ, there exists k : ℕ , (N ≤ k)%nat ∧ P m (a k)).
    We claim that H1 : (∀ (m : ℕ),  ∃ g : ℕ → ℕ, ∀ N : ℕ, (N ≤ g N)%nat ∧ (P m (a (g N)))).
    {
        Take m : ℕ.
        apply choice with (R := fun (k : ℕ) (l : ℕ) ↦ ((k ≤ l)%nat ∧ P m (a l))).
        Apply ex_next.
    }
    apply choice with (R := fun (m : ℕ) (h : ℕ → ℕ) ↦ ( ∀ N : ℕ, (N ≤ h N)%nat ∧ P m (a (h N)) ) ).
    Apply H1.
Qed.


(** The next definition captures what it means to be an index sequence.*)
Definition is_index_seq (n : ℕ → ℕ) :=
    ∀ k : ℕ, (n k < n (S k))%nat.
(** Given the function that produces 'good' elements, we can use it to construct a subsequence by induction.*)
Fixpoint create_seq 
  (f : ℕ → ℕ → ℕ) (l : ℕ) :=
  match l with
  | O => f O O
  | S k => f l (S (create_seq f k))
  end.



(** If the function that produces 'good' elements is such that the produced elements are far enough in the sequence, it is certain that the produced sequence is an index sequence.*)
Lemma created_seq_is_index_seq :
  ∀ (g : ℕ → ℕ → ℕ),
    (∀ (m N : ℕ), (g m N ≥ N)%nat ) ⇒
      is_index_seq (create_seq g).
Proof.
    Take g : (ℕ → ℕ → ℕ).
    Assume g_large : (∀ (m N : ℕ), (g m N ≥ N)%nat ).
    Expand the definition of is_index_seq.
    That is, write the goal as (for all k : ℕ, (create_seq g k < create_seq g (S k))%nat).
    Take k : ℕ.
    Rewrite using (create_seq g (S k) = g (S k) (S (create_seq g k))).
    By g_large it holds that H1 : (g (S k) (S (create_seq g k)) ≥ S(create_seq g k))%nat.
    This follows immediately. 
Qed.


(** 
The next lemma records that indeed the elements in the subsequence satisfy the desired property.*)
Lemma subseq_sat_rel :
  ∀ (a : ℕ → ℝ) (g : ℕ → ℕ → ℕ) (P : ℕ → ℝ → Prop),
    (∀ m N : ℕ, P m (a (g m N)) ) ⇒ 
      ∀ k : ℕ, P k (a (create_seq g k)).
Proof.
    Take a : (ℕ → ℝ).
    Take g : (ℕ → ℕ → ℕ).
    Take P : (ℕ → ℝ → Prop).
    Assume relation_satisfied : (∀ m N : ℕ, P m (a (g m N)) ).
    induction k as [|k IH].
    simpl.
    (** We need to show that $P(0, a (f(0,0)))$ holds. *)
    Apply relation_satisfied.
    Simplify what we need to show.
    We need to show that (P (S k) (a (g (S k) (S (create_seq g k))))). 
    Apply relation_satisfied.
Qed.



Lemma exists_good_subseq :
  ∀ (a : ℕ → ℝ) (P : ℕ → ℝ → Prop),
    (∀ (m : ℕ) (N : ℕ), ∃ k : ℕ, (N ≤ k)%nat ∧ (P m (a k))) ⇒
      ∃ n : ℕ → ℕ, is_index_seq n ∧ ∀ k : ℕ, P k (a (n k)).
Proof.
    Take a : (ℕ → ℝ).
    Take P : (ℕ → ℝ → Prop).
    Assume large_good_el_exist : (for all m N : ℕ, there exists k : ℕ , (N ≤ k)%nat ∧ P m (a k)).
    By existence_next_el_to_fun it holds that  
    H1 : (∃ g : ℕ → ℕ → ℕ, ∀ (m : ℕ) (N : ℕ), (N ≤ g m N)%nat ∧ P m (a (g m N))).
    Choose g such that g_choice_fun according to H1.
    Choose n := (create_seq g).
    We claim that H2 : (∀ (m : ℕ) (M : ℕ), (M ≤ g m M)%nat).
    Take m : ℕ.
    Take M : ℕ.
    By g_choice_fun it holds that H3 : ((M ≤ g m M)%nat ∧ P m (a (g m M))).
    This follows immediately.
    By created_seq_is_index_seq it holds that H4 : (is_index_seq (create_seq g)).
    We claim that H5 : (∀ (m : ℕ) (M : ℕ), P m (a (g m M))).
    Take m : ℕ.
    Take M : ℕ.
    By g_choice_fun it holds that H3 : ((M ≤ g m M)%nat ∧ P m (a (g m M))).
    Because H3 both g_large and g_sat. 
    trivial.
    We claim that H6 : (∀ k : ℕ, P k (a (create_seq g k))).
    Apply subseq_sat_rel; assumption.
    This concludes the proof.
Qed.


Definition is_increasing (f : ℕ → ℕ) :=
  ∀ k : ℕ, (f k ≤ f (S k))%nat.
Lemma incr_loc_to_glob :
  ∀ g : ℕ → ℕ,
    is_increasing g
      ⇒ (∀ k l : ℕ, (k ≤ l)%nat ⇒ (g k ≤ g l)%nat).
Proof.
    Take g : (ℕ → ℕ). 
    Expand the definition of is_increasing.
    That is, write the goal as ((for all k : ℕ, (g k ≤ g (S k))%nat) 
      ⇨ for all k l : ℕ, (k ≤ l)%nat ⇨ (g k ≤ g l)%nat).
    Assume incr_loc : (∀ k : ℕ, (g k ≤ g (S k))%nat).
    Take k : ℕ. 
    induction l as [|l IH_l].

    (** We first need to show that if $k \leq 0$ then $(f (k) \leq f(0))$.*)
    Assume k_le_0 : (k ≤ 0)%nat.
    Rewrite using (k = 0)%nat.
    We need to show that (g 0 ≤ g 0)%nat.
    This follows immediately.

    (** Next, we need to show that if $k \leq S (l)$ then $f(k) \leq f(S (l))$.*)
    Assume Sk_le_Sl : (k ≤ S l)%nat.
    destruct (lt_eq_lt_dec k (S l)) as [temp | k_gt_Sl].
    destruct temp as [k_lt_Sl | k_eq_Sl].
    (** We first consider the case that $k < S(l)$.*)
    It holds that k_le_l : (k ≤ l)%nat.
    By IH_l it holds that gk_le_gl : (g k ≤ g l)%nat.
    It holds that gl_le_g_Sl : (g l ≤ g (S l))%nat.
    This follows immediately.
    (** We now consider the case $k = S(l)$. We need to show that $f(k) \leq f(S(l))$. *)
    Rewrite using (k = S l).
    This follows immediately.
    (** Finally we consider the case $k > S(l)$. However, this case is in contradiction with $k \leq S(l)$. *)
    It holds that not_Sl_lt_k : (¬(S l < k)%nat). 
    Contradiction.
Qed.


Lemma index_seq_strictly_incr :
  ∀ n : ℕ → ℕ, is_index_seq n ⇒ (is_increasing (fun (k : ℕ) ↦ (n k - k)%nat)).
Proof.
    Take n : (ℕ → ℕ). 
    Assume n_is_index_seq : (is_index_seq n).
    Expand the definition of is_increasing.
    That is, write the goal as (for all k : ℕ, (n k - k ≤ n (S k) - S k)%nat).
    Take k : ℕ.
    Expand the definition of is_index_seq in n_is_index_seq.
    That is, write n_is_index_seq as (for all k0 : ℕ, (n k0 < n (S k0))%nat).
    It holds that H1 : (n k < n (S k))%nat.
    This follows immediately.
Qed.



Lemma index_seq_grows_0 :
  ∀ n : ℕ → ℕ, is_index_seq n ⇒ ∀ k : ℕ, (n k ≥ k)%nat.
Proof.
    Take n : (ℕ → ℕ). 
    Assume n_is_index_seq : (is_index_seq n).
    induction k as [|k IH].
    This follows immediately.
    Expand the definition of is_index_seq in n_is_index_seq.
    That is, write n_is_index_seq as (for all k0 : ℕ, (n k0 < n (S k0))%nat).
    It holds that H1 : (n k < n (S k))%nat.
    This follows immediately.
Qed.


Lemma index_seq_grows :
  ∀ n : ℕ → ℕ, is_index_seq n ⇒ (∀ k l : ℕ, (k ≤ l)%nat ⇒ (n k - k ≤ n l - l)%nat).
Proof.
    Take n : (ℕ → ℕ). 
    Assume n_is_index_seq : (is_index_seq n).
    Define g := (fun (k : ℕ) ↦ (n k - k)%nat).
    We claim that H1 : (is_increasing g).
    {
        Expand the definition of is_increasing.
        That is, write the goal as (for all k : ℕ, (g k ≤ g (S k))%nat).
        Take k : ℕ.
        Rewrite using (g k = (n k - k))%nat.
        Rewrite using (g (S k) = (n (S k ) - (S k)))%nat.
        Expand the definition of is_index_seq in n_is_index_seq.
        That is, write n_is_index_seq as (for all k0 : ℕ, (n k0 < n (S k0))%nat).
        Apply (index_seq_strictly_incr n).
        This follows immediately.
    }
    By incr_loc_to_glob it holds that H2 : (∀ k l : ℕ, (k ≤ l)%nat ⇒ (g k ≤ g l)%nat).
    Take k : ℕ. 
    Take l : ℕ. 
    Assume k_le_l : (k ≤ l)%nat.
    By H2 it holds that H3 : (g k ≤ g l)%nat.
    This follows by assumption.
Qed.



(** ## Constructing a subsequence with elements satisfying a particular property

Given a property $P : \mathbb{N} → \mathbb{R} → \mathrm{Prop}$, and given that it holds for infinitely many elements in the sequence, we want to find a subsequence with all elements satisfying the property. *)
(** ### Finding the smallest element satisfying the property

This seems to require some decidability on the property*)
Fixpoint first_satisfying_element_helper
  (rel : ℕ → ℕ → bool)
  (k : ℕ)
  (N : ℕ) :=
  match k with
  | O => N
  | S l => if (rel (N-k)%nat (N-k)%nat) 
                then k
                else (first_satisfying_element_helper rel l N)
  end.  
Definition first_satisfying_element
  (rel : ℕ → ℕ → bool)
  (l : ℕ)
  (N : ℕ)
  := first_satisfying_element_helper rel (N-l) N.  
(** ### From infinitely many elements to a function producing those elements*)
Lemma inf_el_to_fun :
  ∀ (a : ℕ → ℝ) (P : ℕ → ℝ → Prop),
    (∀ N : ℕ, ∃ k : ℕ, (N ≤ k)%nat ∧ (P N (a k))) ⇒
      ∃ f : ℕ → ℕ, ∀ l : ℕ, (l ≤ f l)%nat ∧ P l (a (f l)).
Proof.
    Take a : (ℕ → ℝ). 
    Take P : (ℕ → ℝ → Prop).
    apply choice with (R := fun (k : ℕ) (l : ℕ) ↦ ((k ≤ l)%nat ∧ P k (a l))).
Qed.


Fixpoint seq_of_max (f : ℕ → ℕ) (l : ℕ) :=
  match l with 
  | O => f O
  | S k => Nat.max (f l) (seq_of_max f k)
  end.


(** ### The sequence of maxima is increasing*)
Lemma seq_of_max_is_increasing :
  ∀ g : ℕ → ℕ, is_increasing (seq_of_max g).
Proof.
    Take g : (ℕ → ℕ).
    Expand the definition of is_increasing.
    That is, write the goal as (for all k : ℕ, (seq_of_max g k ≤ seq_of_max g (S k))%nat).
    Take k : ℕ. 
    Simplify what we need to show. 
    This follows immediately.
Qed.


Lemma elements_le_seq_of_max_pre :
  ∀ (g : ℕ → ℕ) (n : ℕ),
    (g n ≤ seq_of_max g n)%nat.
Proof.
    Take g : (ℕ → ℕ).
    induction n as [|n IH_n].
    (** We first consider the base case $n=0$.*)
    Expand the definition of seq_of_max.
    That is, write the goal as ((g 0 ≤ g 0)%nat).
    (** We need to show that $f( 0 ) \leq f( 0)$.*)
    This follows immediately.
    (** Next we consider the general case. We need to show that $f(S(n))\leq \mathsf{seqofmax}(f, S(n))$. *)
    Expand the definition of seq_of_max.
    That is, write the goal as ((g (S n) ≤ Nat.max (g (S n))
     ((fix seq_of_max (f : ℕ ⇨ ℕ) (l : ℕ) {struct l} : ℕ :=
         match l with
         | 0 => f 0
         | S k => Nat.max (f l) (seq_of_max f k)
         end) g n))%nat).
    (** By the definition of $\mathsf{seqofmax}(f,S(n))$ as the maximum of $f(S(n))$ and another number, this*)
    This follows immediately.
Qed.


Lemma elements_le_seq_of_max :
  ∀ (g : ℕ → ℕ) (n : ℕ) (k : ℕ),
    (k ≤ n)%nat ⇒ (g k ≤ seq_of_max g n)%nat.
Proof.
    Take g : (ℕ → ℕ).
    Take n : ℕ.
    Take k : ℕ.
    Assume k_le_n : (k ≤ n)%nat. 
    By elements_le_seq_of_max_pre it holds that H1 : (g k ≤ seq_of_max g k)%nat.
    We claim that H2 : (seq_of_max g k ≤ seq_of_max g n)%nat.
    Apply incr_loc_to_glob. 
    Apply seq_of_max_is_increasing.
    Apply k_le_n.
    (** By transitivity, the conclusion follows immediately. *)
    This follows immediately.
Qed.


(** ### From a function producing the correct elements to an index sequence*)
Fixpoint build_seq 
  (f : ℕ → ℕ) 
  (k : ℕ) :=
  match k with 
  | O => f O
  | S m => f (S (seq_of_max f (build_seq f m)))
  end.
Lemma built_seq_is_index_seq :
  ∀ g : ℕ → ℕ,
    (∀ k : ℕ, (g k ≥ k)%nat) ⇒
      is_index_seq (build_seq g).
Proof.
    Take g : (ℕ → ℕ).
    Assume for_all_k_g_k_ge_k : (for all k : ℕ, (g k ≥ k)%nat).
    Expand the definition of is_index_seq.
    That is, write the goal as (for all k : ℕ, (build_seq g k < build_seq g (S k))%nat).
    Take l : ℕ.
    Rewrite using (build_seq g (S l) = g( S(seq_of_max g (build_seq g l))))%nat.
    We claim that H1 : (g( S(seq_of_max g (build_seq g l)))≥ S(seq_of_max g (build_seq g l)))%nat.
    Apply for_all_k_g_k_ge_k.
    It holds that H2 : (g( S(seq_of_max g (build_seq g l)))> seq_of_max g (build_seq g l))%nat.
    We claim that H3 : (seq_of_max g (build_seq g l) ≥ g(build_seq g l))%nat.
    Apply elements_le_seq_of_max_pre.
    By for_all_k_g_k_ge_k it holds that H4 : (g(build_seq g l) ≥ build_seq g l)%nat.
    This concludes the proof.
Qed.
(** ### Subsequence satisfies relation*)
