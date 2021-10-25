(** * Sequences

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
Require Import ClassicalChoice.

Require Import Waterproof.AllTactics.
Require Import Waterproof.load_database.RealsAndIntegers.
Require Import Waterproof.notations.notations.
Require Import Waterproof.set_search_depth.To_5.
Require Import Waterproof.set_intuition.Disabled.
Require Import Waterproof.load_database.DisableWildcard.

Global Hint Resolve Rabs_Rabsolu : reals.
Global Hint Resolve Rabs_minus_sym : reals.
Global Hint Resolve Rmult_lt_0_compat : reals.
Global Hint Resolve Rinv_lt_contravar : reals.

Open Scope extra.

(** ** What is a sequence of real numbers?

A sequence of real numbers is a function from the natural numbers to the real numbers. So a function $a_seq : \mathbb{N} → \mathbb{R}$ is a sequence.*)

(** ### Examples of sequences

Let us give a few examples of sequences of real numbers. The first example is the sequence $a_seq : ℕ → ℝ$ defined by 

$$a_seq := \mathsf{fun} \   n \mapsto \mathsf{INR}(n) + 2.$$

In Waterproof, we can write this as*)

Definition a_seq : ℕ → ℝ := fun n ↦ INR(n) + 2.
(** We could also have written that $a_seq: \mathbb{N} → ℝ$ is defined by $(a_seq)_n := \mathsf{INR} (n) + 2$, and usually we just leave out the function $\mathsf{INR}$ and would write $(a_seq)_n := n + 2$.*)
(** 
Another example is the sequence $y_seq: ℕ → ℝ$ defined by $(y_seq)_n := 3$. The sequence $y_seq$ is just constant! Within Waterproof, we could define the sequence $y_seq$ by
```
Definition y_seq : ℕ → ℝ := 3.
```

However, let us also give an alternative way, which looks a  bit closer to the definition $y_seq_n := 3$.*)

Definition y_seq (n : ℕ) := 3.
(** ## Terminology about sequences

We call the function values $a(0)$, $a(1)$, $a(2)$, $\dots$ the **elements** of the sequence. Instead of $a(n)$, in mathematics we often write $a_n$. Moreover, instead of writing *let $a : \mathbb{N} \to \mathbb{R}$ be a sequence*, one often writes *let $(a_n)_{n \in \mathbb{N}}$ be a sequence*, or even shorter *let $(a_n)$ be a sequence*. 

The reason for the name *sequence* becomes clearer by writing the elements in a row, i.e. in a sequence,
$$
a_0, a_1, a_2, a_3, a_4, a_5, a_6, a_7, a_8, \dots
$$

However convenient and intuitive this notation is, it can also become confusing if you forget that a sequence of real numbers is *really* a function from the natural numbers to the real numbers.*)
(** ## Asymptotic behavior of sequences

Analysis all revolves around questions such as: what happens if a parameter gets very small? What happens if a parameter gets very large?

For sequences, the interesting question is: what can we say about the elements $a_n$ when $n$ gets very large? Think for instance about the sequence $a_n := 1/n$. Then we might want to say: when $n$ gets very large, the element $a_n$ is very close to zero.

The only thing is, that we need to make the previous sentence much more precise if we want to work with it in mathematics. For all $\epsilon : ℝ$, if $ε > 0$, then there is a certain threshold $N : ℕ$ such that for all $n: ℕ$, if $n \geq N$ then $a_n$ is within distance $\epsilon$ from $0$.`*)
(** The definition of `cv_to` is completely equivalent to the definition of `Un_cv` in the standard library. *)
Lemma convergence_equivalence : converges_to = Un_cv.
Proof.
    trivial.
Qed.


(** ## Preparation for a simple limit*)
Lemma archimed_mod :
  ∀ x : ℝ, ∃ n : ℕ, INR(n) > x.
Proof.
    Take x : ℝ.
    Either (x <= 0) or (0 < x).
    - Case (x <= 0).
      Choose n := 1%nat.
      We claim that H1 : (INR 1 > INR 0).
      Expand the definition of INR.
      That is, write the goal as ( 1 > 0 ).
      This follows immediately.
      Rewrite using (0 = INR(0)) in r.
      It follows that (INR 1 > x).
    - Case (0 < x).
      By archimed it holds that H2 : (IZR( up x) > x ∧ IZR( up x ) - x ≤ 1).
      It holds that H3 : (IZR( up x ) > x).
      It holds that H4 : (0 < IZR( up x )).
      By lt_0_IZR it holds that H5 : (0 < up x)%Z.
      It holds that H6 : (0 <= up x)%Z.
      By IZN it holds that H7 : (∃ k : ℕ, up x = Z.of_nat k).
      Choose k such that up_x_is_k according to H7.
      Choose n := k.
      We need to show that (INR k > x).
      By INR_IZR_INZ it holds that H8 : (INR k = IZR (Z.of_nat k)).
      Rewrite using (INR k = IZR (Z.of_nat n)).
      Rewrite using (Z.of_nat n = up x).
      This follows by assumption.
Qed.


(** Next, we introduce eventually equal sequences, and show that they converge to the same limit.*)
Definition evt_eq_sequences (a b : ℕ → ℝ) := (∃ k : ℕ,
      ∀ n : ℕ, (n ≥ k)%nat ⇒ a n = b n).

Lemma conv_evt_eq_seq :
  ∀ (a b : ℕ → ℝ) (l : ℝ), (evt_eq_sequences a b) ⇒ (a ⟶ l) ⇒ (b ⟶ l).
Proof.
    Take a, b : (ℕ → ℝ), l : ℝ.
    Assume a_b_similar : (evt_eq_sequences a b) and a_to_l : (a ⟶ l).
    To show: (∀ ε : ℝ, ε > 0 ⇒ ∃ N : ℕ, ∀ n : ℕ, (n ≥ N)%nat ⇒ ｜(b n) - l ｜ <ε).
    Expand the definition of converges_to.
    That is, write the goal as (for all ε : ℝ, ε > 0 ⇨ there exists N : ℕ,
      for all n : ℕ, (n ≥ N)%nat ⇨ ｜ b n - l ｜ < ε ).
    Take ε : ℝ; such that ε_gt_0 : (ε > 0).
    Choose n1 such that a_close_to_l according to (a_to_l ε ε_gt_0).
    Choose k such that an_is_bn_for_n_ge_k according to a_b_similar.
    Choose M := (Nat.max n1 k).
    It holds that M_ge_n1 : (M ≥ n1)%nat.
    Take n : ℕ; such that n_ge_M : (n ≥ M)%nat.
    We claim that n_ge_n1 : (n ≥ n1)%nat.
    This follows immediately.
    It holds that an_eq_bn : (a n = b n).
    We claim that an_close_to_l : (|(a n) - l | < ε).
    Apply (a_close_to_l n).
    This follows immediately.
    Rewrite using (b n = a n).
    Apply an_close_to_l.
Qed.



(** From this, it is fairly easy to prove that sequences that are exactly the same also converge to the same limit.
We do this by first using the lemma, and then proving that the sequences are indeed eventually equal.*)

Lemma eq_seq_conv_to_same_lim :
  ∀ (a : ℕ → ℝ) (b : ℕ → ℝ) (l : ℝ),
    (∀ n : ℕ, a n = b n) ⇒ a ⟶ l ⇒ b ⟶ l.
Proof.
    Take a, b : (ℕ → ℝ), l : R.
    Take seq_eq : (for all n : ℕ, a n = b n).
    Apply conv_evt_eq_seq.
    (** By our lemma, it suffices to prove that (evt_eq_sequences a b) *)
    We need to show that (∃ k : ℕ, ∀ n : ℕ, (n ≥ k)%nat ⇒ a n = b n).
    Expand the definition of evt_eq_sequences.
    That is, write the goal as (there exists k : ℕ, 
      for all n : ℕ, (n ≥ k)%nat ⇨ a n = b n ).
    Choose k := O.
    Take n : ℕ; such that n_gt_k : (n ≥ k)%nat.
    This follows immediately.
Qed.



(** ## A simple limit

The simplest sequence we can think of is the constant sequence, e.g. $1, 1, 1, 1, 1, ...$.
We can generalise this to any real number $c$, and define the constant sequence $s_n = c, ∀ n : \mathbb{N}$.
Since we can choose $n$ as large as possible, without changing the value of $s_n$, this sequences clearly converges to its constant value $c$, i.e. $\lim_{n \to \infty} s_n = c$.*)
Definition constant_sequence (c : ℝ) := fun (n : ℕ) ↦ c.
Lemma lim_const_seq :
  ∀ (c : ℝ), constant_sequence c ⟶ c.
Proof.
    Take c : ℝ.
    Define s := (constant_sequence c).
    To show: (∀ ε : ℝ, ε > 0 ⇒ ∃ N : ℕ, ∀ n : ℕ, (n ≥ N)%nat ⇒ ｜(s n) - c｜ < ε).
    Expand the definition of converges_to.
    That is, write the goal as (for all ε : ℝ, ε > 0 ⇨ there exists N : ℕ,
      for all n : ℕ, (n ≥ N)%nat ⇨ ｜ s n - c ｜ < ε).
    Take ε : ℝ; such that ε_gt_0 : (ε > 0).
    Choose Nn := O.
    Take n : ℕ; such that n_ge_Nn : (n ≥ Nn)%nat.
    It holds that H : (s n = c).
    Rewrite using (s n = c).
    By R_dist_eq it holds that H2 : (｜c - c｜ = 0).
    We conclude that (｜c - c｜ < ε).
Qed.

(** #### **Another simple limit**

Next, we consider another rather simple sequence, namely $1, \frac{1}{2}, \frac{1}{3}, \frac{1}{4}, ...$.
We can denote the sequence as follows:
$$
  d_n = \frac{1}{n+1}.
$$
This is a bit more involved than the constant sequence, since the value of our sequence now depends on $n$.
Still, it is easy to see that when $n$ increases, the value of $d_n$ converges to $0$.*)
Definition d := fun (n : ℕ) ↦ 1 / (n + 1).

Lemma lim_d_0 : Un_cv d 0.
Proof.
    Expand the definition of d.
    That is, write the goal as ( Un_cv (n) ↦ (1 / (n + 1)) 0 ).
    Expand the definition of Un_cv.
    That is, write the goal as (for all eps : ℝ, eps > 0 
      ⇨ there exists N : ℕ, for all n : ℕ, (n ≥ N)%nat 
      ⇨ ｜ 1 / (n + 1) - 0 ｜ < eps ).
    Take ε : ℝ.
    Assume ε_gt_0 : (ε > 0).
    Choose n1 such that H_large according to (archimed_mod (/ε)).
    Choose N := n1.
    Take n : ℕ. 
    Assume n_ge_N : (n ≥ n1)%nat.
    Expand the definition of R_dist.
    That is, write the goal as ( | 1 / (n + 1) - 0 | < ε ).
    Apply Rabs_def1.
    Rewrite using (1 / (INR n + 1) - 0 = 1 / (INR n + 1)).
    We need to show that (1 / (INR n+1) < ε ).
    It holds that Rininv_eps : (/ / ε = ε). 
    Rewrite using (ε = / / ε).
    We need to show that (1 / (INR n+1) < / / ε ).
    Rewrite using (1/(INR n+1) = /(INR n+1)).
    We need to show that (/ (INR n+1) < / / ε ).
    Apply (Rinv_lt_contravar : for all r1 r2 : R, 0 < r1 * r2 -> r1 < r2 -> / r2 < / r1).
    We need to show that (0 < / ε * (INR n + 1)).
    This follows immediately.
    It holds that H2 : (/ ε < INR n1).
    By le_INR it holds that H3 : (INR n1 ≤ INR n ).
    It holds that H4 : (INR n < INR n + 1).
    We need to show that (/ ε < INR n + 1 ).
    This follows immediately.
    Rewrite using (1/(INR n + 1) - 0 = / (INR n + 1)).
    It holds that H6 : (INR n >= 0).
    It holds that H7 : (INR n + 1 > 0).
    It holds that H8 : (0 < /(INR n + 1)).
    This concludes the proof.
Qed.


Lemma min_1_over_n_plus_1_to_0 :
  Un_cv (fun (n : ℕ) ↦ - (1 / (INR(n) + 1))) 0.
Proof.
    By lim_d_0 it holds that H1 : (Un_cv d 0).
    By (CV_opp) it holds that H2 : (Un_cv (opp_seq d) (-0)).
    Rewrite using (-0 = 0) in H2.
    Expand the definition of opp_seq in H2.
    That is, write H2 as ( Un_cv (n) ↦ (- d n) 0 ).
    Expand the definition of d in H2.
    That is, write H2 as ( Un_cv (n) ↦ (- (1 / (n + 1))) 0 ).
    This follows by assumption.
Qed.



(** ## The squeeze theorem*)
Theorem squeeze_theorem :
  ∀ (a : ℕ → ℝ) (b : ℕ → ℝ) (c : ℕ → ℝ) (l : ℝ),
    (∀ n : ℕ, a n ≤ b n ∧ b n ≤ c n) ⇒
      a ⟶ l ⇒ c ⟶ l ⇒ b ⟶ l.
Proof.
    Take a, b, c : (ℕ ⇨ ℝ), l : ℝ.
    Assume b_squeezed : (∀ n : ℕ, a n ≤ b n ∧ b n ≤ c n) and a_cv_to_l : (a ⟶ l).
    Assume c_cv_to_l : (c ⟶ l).
    To show: (∀ ε : ℝ, ε > 0 ⇒ ∃ N : ℕ, ∀ n : ℕ, (n ≥ N)%nat ⇒ ｜b n - l｜ < ε).
    Expand the definition of converges_to.
    That is, write the goal as (for all ε : ℝ, ε > 0 
      ⇨ there exists N : ℕ, for all n : ℕ, (n ≥ N)%nat 
      ⇨ ｜ b n - l ｜ < ε ).
    Take ε : ℝ; such that ε_gt_0 : (ε > 0). 
    Choose Na such that a_close_to_l according to (a_cv_to_l ε ε_gt_0).
    Choose Nc such that c_close_to_l according to (c_cv_to_l ε ε_gt_0).
    Choose Nn := (Nat.max Na Nc).
    Take n : ℕ; such that n_ge_N : (n ≥ Nn)%nat.
    It holds that n_ge_Na : (n ≥ Na)%nat.
    It holds that d_an_l_lt_ε : (R_dist (a n) l < ε).
    Expand the definition of R_dist in d_an_l_lt_ε.
    That is, write d_an_l_lt_ε as ( | a n - l | < ε ).
    Rewrite using (Rabs( a n - l  ) = Rabs( l - a n)) in d_an_l_lt_ε.
    By Rabs_def2 it holds that H2 : (l - a n < ε ∧- ε < l - a n).
    It holds that H3 : (- ε < l - a n).
    It holds that n_ge_Nc : (n ≥ Nc)%nat.
    It holds that d_cn_l_lt_ε : (R_dist (c n) l < ε).
    Expand the definition of R_dist in d_cn_l_lt_ε.
    That is, write d_cn_l_lt_ε as ( | c n - l | < ε ).
    By Rabs_def2 it holds that H4 : (c n - l < ε ∧ - ε < c n - l).
    It holds that H5 : (c n - l < ε).
    Expand the definition of R_dist.
    That is, write the goal as ( | b n - l | < ε ).
    Apply Rabs_def1. 
    By b_squeezed it holds that H6 : (a n ≤ b n ∧ b n ≤ c n).
    By b_squeezed it holds that H7 : (a n ≤ b n). 
    We need to show that ( b n - l < ε).
    This follows immediately.
    It holds that H6 : (a n ≤ b n ∧ b n ≤ c n).
    By b_squeezed it holds that H8 : (b n ≤ c n).
    We need to show that (- ε < b n - l).
    This follows immediately.
Qed.


Lemma upp_bd_seq_is_upp_bd_lim :
  ∀ (a : ℕ → ℝ) (L M: ℝ),
    (∀ n : ℕ, a n ≤ M) ⇒ 
      (Un_cv a L) ⇒ L ≤ M.
Proof.
    Take a : (ℕ → ℝ).
    Take L : ℝ.
    Take M : ℝ.
    Take a_bdd_by_M : (∀ n : ℕ, (a n) ≤ M).
    Assume a_cv_to_L : (Un_cv a L).
    By Rle_or_lt it holds that H : (L ≤ M ∨ M < L).
    Because H either L_le_M or M_lt_L.
    Case (L ≤ M).
    It follows that (L ≤ M).
    Case (M < L).
    Define ε := (L-M).
    Expand the definition of Un_cv in a_cv_to_L.
    That is, write a_cv_to_L as (for all eps : ℝ, eps > 0 
      ⇨ there exists N : ℕ, for all n : ℕ, (n ≥ N)%nat 
      ⇨ ｜ a n - L ｜ < eps).
    We claim that H2 : (∃ N : ℕ, ∀n : ℕ, (n ≥ N)%nat ⇒ R_dist (a n) L < ε).
    Apply a_cv_to_L. 
    It holds that H3 : (L - M > 0). 
    It follows that (ε > 0).

    Choose Nn such that a_close_to_L according to H2.
    It holds that H4 : (R_dist (a Nn) L < ε).
    Expand the definition of R_dist in H4.
    That is, write H4 as ( | a Nn - L | < ε ).
    By Rabs_def2 it holds that H5 : (a Nn - L < ε ∧ (- ε < a Nn - L)).
    It holds that H6 : (- ε < a Nn - L).
    It holds that H7 : (a Nn ≤ M).
    Rewrite using (ε = L - M) in H6.
    It follows that (L ≤ M).
Qed.


Lemma low_bd_seq_is_low_bd_lim :
  ∀ (a : ℕ → ℝ) (L M: ℝ),
    (∀ n : ℕ, a n ≥ M) ⇒ 
      (Un_cv a L) ⇒ L ≥ M.
Proof.
    Take a : (ℕ → ℝ).
    Take L : ℝ.
    Take M : ℝ.
    Take a_bdd_by_M : (∀ n : ℕ, a n ≥ M).
    Define b := (opp_seq a).
    Assume a_cv_to_L : (Un_cv a L).
    Expand the definition of opp_seq in b.
    That is, write b as ( ℕ ⇨ ℝ ). (*TODO *)
    We claim that H : (Un_cv b (-L)).
    Apply CV_opp.
    This follows by assumption.
    We claim that H1 : (-L ≤ -M).
    Apply (upp_bd_seq_is_upp_bd_lim b).
    We need to show that (for all n : ℕ, b n ≤ - M).
    Take n : ℕ. 
    Rewrite using (b = opp_seq a).
    Expand the definition of opp_seq.
    That is, write the goal as (-(a n) ≤ -M).
    This follows immediately.
    We need to show that (Un_cv b (-L)).
    This follows immediately.
    It follows that (L ≥ M).
Qed.


(** ## Order and limits*)
Lemma seq_ordered_lim_ordered :
  ∀ (a b: ℕ → ℝ) (m l : ℝ),
    Un_cv a m ⇒ Un_cv b l ⇒
    (∀ n : ℕ, a n ≤ b n) ⇒ m ≤ l.
Proof.
    Take a : (ℕ → ℝ).
    Take b : (ℕ → ℝ).
    Take m : ℝ.
    Take l : ℝ.
    Assume a_cv_to_m : (Un_cv a m) and b_cv_to_l : (Un_cv b l).
    Assume a_b_ordered : (∀ n : ℕ, a n ≤ b n).
    By Rle_or_lt it holds that H1 : (m ≤ l ∨ l < m).
    Because H1 either m_le_l or l_lt_m.
    Case (m ≤ l).
    Apply m_le_l.
    Case (l < m).
    Define ε := ((m - l)/2).
    Expand the definition of Un_cv in b_cv_to_l.
    That is, write b_cv_to_l as (for all eps : ℝ, eps > 0 
      ⇨ there exists N : ℕ, for all n : ℕ, (n ≥ N)%nat
      ⇨ ｜ b n - l ｜ < eps).
    Expand the definition of Un_cv in a_cv_to_m.
    That is, write a_cv_to_m as (for all eps : ℝ, eps > 0 
      ⇨ there exists N : ℕ, for all n : ℕ, (n ≥ N)%nat 
      ⇨ ｜ a n - m ｜ < eps ).
    It holds that H2 : (m-l > 0).
    It holds that H3 : ((m-l)/2 > 0).
    It holds that H4 : (ε > 0).
    It holds that H5 : (∃ N1 : ℕ, ∀ n : ℕ, (n ≥ N1)%nat ⇒ R_dist (b n) l < ε).
    It holds that H6 : (∃ N2 : ℕ, ∀ n : ℕ, (n ≥ N2)%nat ⇒ R_dist (a n) m < ε).
    Choose N1 such that H7 according to H5.
    Choose N2 such that H8 according to H6.
    Define N3 := (Nat.max N1 N2).
    It holds that H9 : (Nat.max N1 N2 ≥ N1)%nat.
    It holds that H10 : (Nat.max N1 N2 ≥ N2)%nat.
    It holds that H11 : (N3 ≥ N1)%nat.
    It holds that H12 : (N3 ≥ N2)%nat.
    It holds that H13 : (R_dist (b N3) l < ε).
    It holds that H14 : (R_dist (a N3) m < ε).
    Expand the definition of R_dist in H13.
    That is, write H13 as ( | b N3 - l | < ε ).
    Expand the definition of R_dist in H14.
    That is, write H14 as ( | a N3 - m | < ε ).
    By Rabs_def2 it holds that H15 : (a N3 - m < ε ∧ - ε < a N3 - m).
    By Rabs_def2 it holds that H16 : (b N3 - l < ε ∧ - ε < b N3 - l).
    It holds that H17 : (a N3 - m < ε).
    It holds that H18 : (- ε < b N3 - l).
    Rewrite using (ε = (m - l)/2) in H17.
    Rewrite using (ε = (m - l)/2) in H18.
    It holds that H19 : (a N3 ≤ b N3).
    It holds that H20 : (ε = (m - l)/2).
    It follows that (m ≤ l).
Qed.
