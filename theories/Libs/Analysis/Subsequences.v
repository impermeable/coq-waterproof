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

Require Import Coq.Reals.Reals.
Require Import ZArith.
Require Import Lra.
Require Import Classical.
Require Import Classical_Pred_Type.
Require Import ClassicalChoice.

Require Import Automation.
Require Import Libs.Negation.
Require Import Notations.
Require Import Tactics.

Require Import Waterprove.

Waterproof Enable Automation RealsAndIntegers.

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
    Assume that (for all m N : ℕ, there exists k : ℕ , (N ≤ k)%nat ∧ P m (a k)) (i).
    We claim that (∀ (m : ℕ),  ∃ g : ℕ → ℕ, ∀ N : ℕ, (N ≤ g N)%nat ∧ (P m (a (g N)))) (ii).
    {
        Take m : ℕ.
        apply choice with (R := fun (k : ℕ) (l : ℕ) ↦ ((k ≤ l)%nat ∧ P m (a l))).
        apply (i).
    }
    apply choice with (R := fun (m : ℕ) (h : ℕ → ℕ) ↦ ( ∀ N : ℕ, (N ≤ h N)%nat ∧ P m (a (h N)) ) ).
    apply (ii).
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
    Assume that (∀ (m N : ℕ), (g m N ≥ N)%nat) (i).
    We need to show that (for all k : ℕ, (create_seq g k < create_seq g (S k))%nat).
    Take k : ℕ.
    By (i) it holds that (g (S k) (S (create_seq g k)) ≥ S(create_seq g k))%nat.
    We conclude that (& create_seq g k < g (S k) (S (create_seq g k)) = create_seq g (S k))%nat.
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
    Assume that (∀ m N : ℕ, P m (a (g m N))) (i).
    induction k. (*TODO: if we use 'We use induction on k.'-tacftic, then we cannot directly match on k + 1 *)
    - We need to show that (P 0%nat (a (g 0%nat 0%nat))).
      By (i) we conclude that (P 0%nat (a (g 0%nat 0%nat))).
    - We need to show that (P (S k) (a (g (S k) (S (create_seq g k))))).
      By (i) we conclude that (P (S k) (a (g (S k) (S (create_seq g k))))).
Qed.



Lemma exists_good_subseq :
  ∀ (a : ℕ → ℝ) (P : ℕ → ℝ → Prop),
    (∀ (m : ℕ) (N : ℕ), ∃ k : ℕ, (N ≤ k)%nat ∧ (P m (a k))) ⇒
      ∃ n : ℕ → ℕ, is_index_seq n ∧ ∀ k : ℕ, P k (a (n k)).
Proof.
    Take a : (ℕ → ℝ).
    Take P : (ℕ → ℝ → Prop).
    Assume that (for all m N : ℕ, there exists k : ℕ , (N ≤ k)%nat ∧ P m (a k)).
    By existence_next_el_to_fun it holds that
      (∃ g : ℕ → ℕ → ℕ, ∀ (m : ℕ) (N : ℕ), (N ≤ g m N)%nat ∧ P m (a (g m N))).
    Obtain such a g. It holds that
      (∀ (m : ℕ) (N : ℕ), (N ≤ g m N)%nat ∧ P m (a (g m N))) (i).
    Choose n := (create_seq g).
    We show both statements.
    - We need to show that (is_index_seq n).
      We need to show that (is_index_seq (create_seq g)).
      By created_seq_is_index_seq it suffices to show that 
        (for all m N : ℕ, (g m N ≥ N)%nat).
      Take m, M : nat.
      By (i) it holds that ((M ≤ g m M)%nat ∧ P m (a (g m M))).
      We conclude that (g m M >= M)%nat.
    - We need to show that (for all k : ℕ, P k (a (n k))).
      We need to show that (for all k : ℕ, P k (a ((create_seq g) k))).
      Fail By subseq_sat_rel it suffices to show that (for all m N : ℕ, P m (a (g m N))). (*TODO: fix*)
      apply subseq_sat_rel.
      Take m : ℕ.
      Take M : ℕ.
      By (i) it holds that ((M ≤ g m M)%nat ∧ P m (a (g m M))) (ii).
      Because (ii) both (M ≤ g m M)%nat and (P m (a (g m M))) hold.
      We conclude that (P m (a (g m M))).
Qed.

Definition is_increasing (f : ℕ → ℕ) :=
  ∀ k : ℕ, (f k ≤ f (S k))%nat.
Lemma incr_loc_to_glob :
  ∀ g : ℕ → ℕ,
    is_increasing g
      ⇒ (∀ k l : ℕ, (k ≤ l)%nat ⇒ (g k ≤ g l)%nat).
Proof.
    Take g : (ℕ → ℕ).
    We need to show that ((for all k : ℕ, (g k ≤ g (S k))%nat) 
      ⇨ for all k l : ℕ, (k ≤ l)%nat ⇨ (g k ≤ g l)%nat).
    Assume that (∀ k : ℕ, (g k ≤ g (S k))%nat).
    Take k : ℕ. 
    induction l as [|l IH_l].

    (** We first need to show that if $k \leq 0$ then $(f (k) \leq f(0))$.*)
    Assume that (k ≤ 0)%nat.
    It holds that (k = 0)%nat.
    We conclude that (& g k = g 0 <= g 0)%nat.

    (** Next, we need to show that if $k \leq S (l)$ then $f(k) \leq f(S (l))$.*)
    Assume that (k ≤ S l)%nat.
    destruct (lt_eq_lt_dec k (S l)) as [temp | k_gt_Sl].
    destruct temp as [k_lt_Sl | k_eq_Sl].
    (** We first consider the case that $k < S(l)$.*)
    It holds that (k ≤ l)%nat.
    By IH_l it holds that (g k ≤ g l)%nat.
    It holds that (g l ≤ g (S l))%nat.
    We conclude that (g k <= g (S l))%nat.
    (** We now consider the case $k = S(l)$. We need to show that $f(k) \leq f(S(l))$. *)
    We conclude that (& g k = g (S l) <= g (S l))%nat.
    (** Finally we consider the case $k > S(l)$. However, this case is in contradiction with $k \leq S(l)$. *)
    It holds that (¬(S l < k)%nat).
    Contradiction.
Qed.


Lemma index_seq_strictly_incr :
  ∀ n : ℕ → ℕ, is_index_seq n ⇒ (is_increasing (fun (k : ℕ) ↦ (n k - k)%nat)).
Proof.
    Take n : (ℕ → ℕ); such that (is_index_seq n).
    We need to show that (for all k : ℕ, (n(k) - k ≤ n(S(k)) - S(k))%nat).
    Take k : ℕ.
    It holds that (for all k0 : ℕ, (n k0 < n (S k0))%nat).
    It holds that (n k < n (S k))%nat.
    We conclude that (n k - k ≤ n (S k) - S k)%nat.
Qed.



Lemma index_seq_grows_0 :
  ∀ n : ℕ → ℕ, is_index_seq n ⇒ ∀ k : ℕ, (n k ≥ k)%nat.
Proof.
    Take n : (ℕ → ℕ); such that (is_index_seq n).
    induction k as [|k IH].
    - We conclude that (n 0 >= 0)%nat.
    - It holds that (for all k0 : ℕ, (n k0 < n (S k0))%nat).
      It holds that (n k < n (S k))%nat.
      We conclude that (n (S k) ≥ S k)%nat.
Qed.


Lemma index_seq_grows :
  ∀ n : ℕ → ℕ, is_index_seq n ⇒ (∀ k l : ℕ, (k ≤ l)%nat ⇒ (n k - k ≤ n l - l)%nat).
Proof.
    Take n : (ℕ → ℕ); such that (is_index_seq n).
    Define g := (fun (k : ℕ) ↦ (n k - k)%nat).
    By index_seq_strictly_incr it holds that (is_increasing g).
    By incr_loc_to_glob it holds that (∀ k l : ℕ, (k ≤ l)%nat ⇒ (g k ≤ g l)%nat).
    Take k : ℕ and l : ℕ; such that(k ≤ l)%nat.
    We need to show that (g k <= g l)%nat.
    We conclude that (g k <= g l)%nat.
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
    We need to show that
      (for all k : ℕ, (seq_of_max g k ≤ seq_of_max g (S k))%nat).
    Take k : ℕ.
    We need to show that (seq_of_max g k ≤ Nat.max (g (S k)) (seq_of_max g k))%nat.
    We conclude that (seq_of_max g k ≤ Nat.max (g (S k)) (seq_of_max g k))%nat.
Qed.


Lemma elements_le_seq_of_max_pre :
  ∀ (g : ℕ → ℕ) (n : ℕ),
    (g n ≤ seq_of_max g n)%nat.
Proof.
    Take g : (ℕ → ℕ).
    We use induction on n.
    - We first show the base case (g(0) ≤ seq_of_max(g, 0))%nat.
      We need to show that (g 0 ≤ g 0)%nat.
      We conclude that (g 0 ≤ g 0)%nat.
    - We now show the induction step.
      Assume that (g(n) <= seq_of_max g n)%nat.
      We need to show that (g(n + 1) ≤ 
        (fix seq_of_max (f : ℕ ⇨ ℕ) (l : ℕ) {struct l} : ℕ :=
          match l with
          | 0 => f(0)
          | S k => Nat.max(f(l), seq_of_max(f, k))
          end)(g, n + 1))%nat.
      It holds that (n + 1 = S n)%nat.
      It suffices to show that (g(n) ≤ seq_of_max(g, n))%nat.
      We conclude that (g(n) ≤ seq_of_max(g, n))%nat.
Qed.


Lemma elements_le_seq_of_max :
  ∀ (g : ℕ → ℕ) (n : ℕ) (k : ℕ),
    (k ≤ n)%nat ⇒ (g k ≤ seq_of_max g n)%nat.
Proof.
    Take g : (ℕ → ℕ).
    Take n : ℕ and k : ℕ; such that (k ≤ n)%nat.
    By elements_le_seq_of_max_pre it holds that (g k ≤ seq_of_max g k)%nat.
    We claim that (seq_of_max g k ≤ seq_of_max g n)%nat.
    { By incr_loc_to_glob it suffices to show that (is_increasing (seq_of_max g)).
      By seq_of_max_is_increasing we conclude that (is_increasing (seq_of_max g)).
    }
    We conclude that (& g k <= seq_of_max g k <= seq_of_max g n)%nat.
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
    Assume that (for all k : ℕ, (g k ≥ k)%nat).
    We need to show that (for all k : ℕ, (build_seq g k < build_seq g (S k))%nat).
    Take k : ℕ.
    We need to show that (build_seq g k < g (S (seq_of_max g (build_seq g k))))%nat.
    It holds that (g( S(seq_of_max g (build_seq g k)))≥ S(seq_of_max g (build_seq g k)))%nat.
    It holds that (g( S(seq_of_max g (build_seq g k)))> seq_of_max g (build_seq g k))%nat.
    By elements_le_seq_of_max_pre it holds that (seq_of_max g (build_seq g k) ≥ g(build_seq g k))%nat.
    It holds that (g(build_seq g k) ≥ build_seq g k)%nat.
    We conclude that (& build_seq g k <= g(build_seq g k)
                                      <= seq_of_max g (build_seq g k)
                                      <  g( S(seq_of_max g (build_seq g k))))%nat.
Qed.
(** ### Subsequence satisfies relation*)
