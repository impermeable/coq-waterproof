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
Require Import Lra.
Require Import Classical.
Require Import Classical_Pred_Type.
Require Import ClassicalChoice.

Require Import Tactics.
Require Import Automation.
Require Import Libs.Reals.
Require Import Notations.

#[export] Hint Resolve Rabs_Rabsolu : wp_reals.
#[export] Hint Resolve Rabs_minus_sym : wp_reals.
#[export] Hint Resolve Rmult_lt_0_compat : wp_reals.
#[export] Hint Resolve Rinv_lt_contravar : wp_reals.

Waterproof Enable Automation RealsAndIntegers.

Open Scope R_scope.

(** ** What is a sequence of real numbers?

A sequence of real numbers is a function from the natural numbers to the real numbers. So a function $a_seq : \mathbb{N} → \mathbb{R}$ is a sequence.*)

(** *** Examples of sequences

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
(** ** Terminology about sequences

We call the function values $a(0)$, $a(1)$, $a(2)$, $\dots$ the **elements** of the sequence. Instead of $a(n)$, in mathematics we often write $a_n$. Moreover, instead of writing *let $a : \mathbb{N} \to \mathbb{R}$ be a sequence*, one often writes *let $(a_n)_{n \in \mathbb{N}}$ be a sequence*, or even shorter *let $(a_n)$ be a sequence*. 

The reason for the name *sequence* becomes clearer by writing the elements in a row, i.e. in a sequence,
$$
a_0, a_1, a_2, a_3, a_4, a_5, a_6, a_7, a_8, \dots
$$

However convenient and intuitive this notation is, it can also become confusing if you forget that a sequence of real numbers is *really* a function from the natural numbers to the real numbers.*)
(** ** Asymptotic behavior of sequences

Analysis all revolves around questions such as: what happens if a parameter gets very small? What happens if a parameter gets very large?

For sequences, the interesting question is: what can we say about the elements $a_n$ when $n$ gets very large? Think for instance about the sequence $a_n := 1/n$. Then we might want to say: when $n$ gets very large, the element $a_n$ is very close to zero.

The only thing is, that we need to make the previous sentence much more precise if we want to work with it in mathematics. For all $\epsilon : ℝ$, if $ε > 0$, then there is a certain threshold $N : ℕ$ such that for all $n: ℕ$, if $n \geq N$ then $a_n$ is within distance $\epsilon$ from $0$.`*)
(** The definition of [cv_to] is completely equivalent to the definition of [Un_cv] in the standard library. *)
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
      We claim that (INR 1 > INR 0).
      { Expand the definition of INR.
        That is, write the goal as ( 1 > 0 ).
        We conclude that (1 > 0).
      }
      It holds that (x <= INR 0).
      We conclude that (n > x).
    - Case (0 < x).
      By archimed it holds that (IZR( up x) > x ∧ IZR( up x ) - x ≤ 1).
      It holds that (IZR( up x ) > x).
      It holds that (0 < IZR( up x )).
      By lt_0_IZR it holds that (0 < up x)%Z.
      It holds that (0 <= up x)%Z.
      By IZN it holds that (∃ k : ℕ, up x = Z.of_nat k).
      Obtain such a k. It holds that (up x = Z.of_nat k) (ii).
      Choose n := k.
      We need to show that (INR k > x).
      By INR_IZR_INZ it holds that (INR k = IZR (Z.of_nat k)).
      (* TODO: better solution *)
      We claim that (IZR (up x) = IZR (Z.of_nat k)).
      { rewrite (ii). reflexivity. }
      We need to show that (x < k).
      We conclude that (& x < up x = Z.of_nat k = k).
Qed.


(** Next, we introduce eventually equal sequences, and show that they converge to the same limit.*)
Definition evt_eq_sequences (a b : ℕ → ℝ) := (∃ k : ℕ,
      ∀ n : ℕ, (n ≥ k)%nat ⇒ a n = b n).

Lemma conv_evt_eq_seq :
  ∀ (a b : ℕ → ℝ) (l : ℝ), (evt_eq_sequences a b) ⇒ (a ⟶ l) ⇒ (b ⟶ l).
Proof.
    Take a, b : (ℕ → ℝ) and l : ℝ.
    Assume that (evt_eq_sequences a b) (i) and (a ⟶ l).
    We need to show that (for all ε : ℝ, ε > 0 ⇨ there exists N : ℕ,
      for all n : ℕ, (n ≥ N)%nat ⇨ |b n - l| < ε ).
    Take ε : ℝ; such that (ε > 0).
    It holds that
      (there exists N : ℕ, for all n : ℕ, (n ≥ N)%nat ⇨ |a n - l| < ε).
    Obtain such an N1.
    By (i) it holds that 
      (there exists K : nat, for all n : ℕ, (n ≥ K)%nat ⇨ a n = b n).
    Obtain such a K.
    Choose M := (Nat.max N1 K).
    Take n : ℕ; such that (n ≥ M)%nat.
    It holds that (b n = a n).
    We conclude that (& |b n - l| = |a n - l| < ε).
Qed.

(** From this, it is fairly easy to prove that sequences that are exactly the same also converge to the same limit.
We do this by first using the lemma, and then proving that the sequences are indeed eventually equal.*)

Lemma eq_seq_conv_to_same_lim :
  ∀ (a : ℕ → ℝ) (b : ℕ → ℝ) (l : ℝ),
    (∀ n : ℕ, a n = b n) ⇒ a ⟶ l ⇒ b ⟶ l.
Proof.
  Take a, b : (ℕ → ℝ) and l : R.
  Assume that (for all n : ℕ, a n = b n).
  By conv_evt_eq_seq it suffices to show that (∃ k : ℕ, ∀ n : ℕ, (n ≥ k)%nat ⇒ a n = b n).
  Choose k := O.
  Take n : ℕ; such that (n ≥ k)%nat.
  We conclude that (a n = b n).
Qed.



(** ** A simple limit

The simplest sequence we can think of is the constant sequence, e.g. $1, 1, 1, 1, 1, ...$.
We can generalise this to any real number $c$, and define the constant sequence $s_n = c, ∀ n : \mathbb{N}$.
Since we can choose $n$ as large as possible, without changing the value of $s_n$, this sequences clearly converges to its constant value $c$, i.e. $\lim_{n \to \infty} s_n = c$.*)
Definition constant_sequence (c : ℝ) := fun (n : ℕ) ↦ c.
Lemma lim_const_seq :
  ∀ (c : ℝ), constant_sequence c ⟶ c.
Proof.
    Take c : ℝ.
    Define s := (constant_sequence c).
    To show: (∀ ε : ℝ, ε > 0 ⇒ ∃ N : ℕ, ∀ n : ℕ, (n ≥ N)%nat ⇒ |(s n) - c| < ε).
    Take ε : ℝ; such that (ε > 0).
    Choose Nn := O.
    Take n : ℕ; such that (n ≥ Nn)%nat.
    It holds that (s n = c).
    We conclude that (& |s n - c| = | c - c | = |0| = 0 < ε).
Qed.

(** *** **Another simple limit**

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
    That is, write the goal as (Un_cv(fun n ↦ (1 / (n + 1)), 0)).
    Expand the definition of Un_cv.
    That is, write the goal as (for all eps : ℝ, eps > 0 
      ⇨ there exists N : ℕ, for all n : ℕ, (n ≥ N)%nat 
      ⇨ ｜ 1 / (n + 1) - 0 ｜ < eps ).
    Take ε : ℝ; such that (ε > 0).
    By archimed_mod it holds that (there exists n : ℕ, n > / ε).
    Obtain such an n1. Choose N := n1.
    Take n : ℕ; such that (n ≥ n1)%nat.
    Expand the definition of Rabs.
    That is, write the goal as (｜1 / (n + 1) - 0｜ < ε).
    It suffices to show that (-ε < 1 / (n + 1) - 0 < ε).
    We show both (-ε < 1 / (n + 1) - 0) and (1 / (n + 1) - 0 < ε).
    - It holds that (0 < n + 1). (* n + 1 > 0 is difficult?*)
      We conclude that (& -ε < 0 < / (n + 1) = 1 / (n + 1) - 0).
    - We claim that (/ ε < n + 1). 
      { We conclude that (& / ε < n1 <= n <= n + 1). }
      We conclude that (& 1 / (n + 1) - 0 = / (n + 1) < / / ε = ε).
Qed.


Lemma min_1_over_n_plus_1_to_0 :
  Un_cv (fun (n : ℕ) ↦ - (1 / (INR(n) + 1))) 0.
Proof.
    By lim_d_0 it holds that (Un_cv d 0).
    By (CV_opp) it holds that (Un_cv (opp_seq d) (-0)) (i).
    Expand the definition of opp_seq in (i).
    That is, write (i) as ( Un_cv (fun n ↦ -d(n), -0)).
    Expand the definition of d in (i).
    That is, write (i) as ( Un_cv (fun n ↦ -(1 / (n + 1)), -0)).
    It holds that (0 = -0).
    (* TODO: make transport automatic *)
    By (eq_ind_r(_, _, fun x => Un_cv (fun n ↦ -(1 / (n + 1)), x), (i))) 
      it suffices to show that (Un_cv (fun n ↦ -(1 / (n + 1)), -0)).
    By (i) we conclude that (Un_cv (fun n ↦ -(1 / (n + 1)), -0)).
Qed.



(** ** The squeeze theorem*)
Theorem squeeze_theorem :
  ∀ (a : ℕ → ℝ) (b : ℕ → ℝ) (c : ℕ → ℝ) (l : ℝ),
    (∀ n : ℕ, a n ≤ b n ∧ b n ≤ c n) ⇒
      a ⟶ l ⇒ c ⟶ l ⇒ b ⟶ l.
Proof.
    Take a, b, c : (ℕ ⇨ ℝ) and l : ℝ.
    Assume that (∀ n : ℕ, a n ≤ b n ∧ b n ≤ c n) and (a ⟶ l).
    Assume that (c ⟶ l).
    To show: (∀ ε : ℝ, ε > 0 ⇒ ∃ N : ℕ, ∀ n : ℕ, (n ≥ N)%nat ⇒ |b n - l| < ε).
    Take ε : ℝ; such that (ε > 0).
    It holds that (∃ N : ℕ, ∀ n : ℕ, (n ≥ N)%nat ⇒ |a n - l| < ε).
    Obtain such an Na.
    It holds that (∃ N : ℕ, ∀ n : ℕ, (n ≥ N)%nat ⇒ |c n - l| < ε).
    Obtain such an Nc.
    Choose Nn := (Nat.max Na Nc).
    Take n : ℕ; such that (n ≥ Nn)%nat.
    We claim that (-ε < a n - l).
    { It holds that (n ≥ Na)%nat.
      It holds that (R_dist (a n) l < ε) (iii).
      Expand the definition of Rabs in (iii).
      That is, write (iii) as (｜a(n) - l｜ < ε).
      By Rabs_def2 it holds that (a n - l < ε /\ -ε < a n - l).
      We conclude that (-ε < a n - l).
    }
    We claim that (c n - l < ε).
    { It holds that (n ≥ Nc)%nat.
      It holds that (R_dist (c n) l < ε) (iii).
      Expand the definition of Rabs in (iii).
      That is, write (iii) as (｜c(n) - l｜ < ε).
      By Rabs_def2 it holds that (c n - l < ε /\ -ε < c n - l).
      We conclude that (c n - l < ε).
    }
    Expand the definition of Rabs.
    That is, write the goal as ((if Rcase_abs(b(n) - l) then - (b(n) - l) else b(n) - l) < ε).
    It suffices to show that (-ε < b n - l < ε).
    It holds that (a n ≤ b n ∧ b n ≤ c n).
    We show both (- ε < b n - l) and ( b n - l < ε).
    - We conclude that (& - ε < a n - l <= b n - l).
    - We conclude that (& b n - l <= c n - l < ε).
Qed.


Lemma upp_bd_seq_is_upp_bd_lim :
  ∀ (a : ℕ → ℝ) (L M: ℝ),
    (∀ n : ℕ, a n ≤ M) ⇒ 
      (Un_cv a L) ⇒ L ≤ M.
Proof.
    Take a : (ℕ → ℝ).
    Take L : ℝ.
    Take M : ℝ.
    Assume that (∀ n : ℕ, (a n) ≤ M).
    Assume that (Un_cv a L) (i).
    By Rle_or_lt it holds that (L ≤ M ∨ M < L) (ii).
    Because (ii) either (L ≤ M) or (M < L) holds.
    - Case (L ≤ M).
      It follows that (L ≤ M).
    - Case (M < L).
      Define ε := (L-M).
      It holds that (ε > 0).
      Expand the definition of Un_cv in (i).
      That is, write (i) as (for all eps : ℝ, eps > 0 
        ⇨ there exists N : ℕ, for all n : ℕ, (n ≥ N)%nat 
        ⇨ ｜ a n - L ｜ < eps).
      It holds that (∃ N : ℕ, ∀n : ℕ, (n ≥ N)%nat ⇒ R_dist (a n) L < ε).
      Obtain such an Nn.
      It holds that (R_dist (a Nn) L < ε) (iv).
      Expand the definition of Rabs in (iv).
      That is, write (iv) as (｜a(Nn) - L｜ < ε).
      By Rabs_def2 it holds that (a Nn - L < ε ∧ (- ε < a Nn - L)).
      It holds that (- ε < a Nn - L).
      It holds that (a Nn ≤ M).
      It holds that (- (L - M) < a Nn - L).
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
    Assume that (∀ n : ℕ, a n ≥ M).
    Define b := (opp_seq a).
    Assume that (Un_cv a L).
    It holds that (b = (fun n => - a n)).
    By CV_opp it holds that (Un_cv b (-L)).
    We claim that (-L ≤ -M).
    { By upp_bd_seq_is_upp_bd_lim it suffices to show that
       (for all n : ℕ, b n ≤ - M).
      Take n : ℕ.
      We conclude that (& b n = - a n <= -M).
    }
    We conclude that (L >= M).
Qed.


(** ** Order and limits*)
Lemma seq_ordered_lim_ordered :
  ∀ (a b: ℕ → ℝ) (m l : ℝ),
    Un_cv a m ⇒ Un_cv b l ⇒
    (∀ n : ℕ, a n ≤ b n) ⇒ m ≤ l.
Proof.
    Take a : (ℕ → ℝ).
    Take b : (ℕ → ℝ).
    Take m : ℝ.
    Take l : ℝ.
    Assume that (Un_cv a m) (i) and (Un_cv b l) (ii).
    Assume that (∀ n : ℕ, a n ≤ b n).
    We argue by contradiction.
    Assume that (~ m <= l).
    It holds that (l < m).
    Define ε := ((m - l)/2).
    It holds that (ε > 0).
    Expand the definition of Un_cv in (ii).
    That is, write (ii) as (for all eps : ℝ, eps > 0 
      ⇨ there exists N : ℕ, for all n : ℕ, (n ≥ N)%nat
      ⇨ ｜ b n - l ｜ < eps).
    Expand the definition of Un_cv in (i).
    That is, write (i) as (for all eps : ℝ, eps > 0 
      ⇨ there exists N : ℕ, for all n : ℕ, (n ≥ N)%nat 
      ⇨ ｜ a n - m ｜ < eps ).
    It holds that (∃ N1 : ℕ, ∀ n : ℕ, (n ≥ N1)%nat ⇒ R_dist (b n) l < ε).
    Obtain such an N1.
    It holds that (∃ N2 : ℕ, ∀ n : ℕ, (n ≥ N2)%nat ⇒ R_dist (a n) m < ε).
    Obtain such an N2.
    Define N3 := (Nat.max N1 N2).
    We claim that (b N3 < a N3).
    { It holds that (R_dist (b N3) l < ε)  (v).
      It holds that (R_dist (a N3) m < ε) (vi).
      Expand the definition of Rabs in (v).
      That is, write (v) as (｜b(N3) - l｜ < ε).
      Expand the definition of Rabs in (vi).
      That is, write (vi) as ( ｜ a N3 - m ｜ < ε ).
      By Rabs_def2 it holds that (a N3 - m < ε ∧ - ε < a N3 - m).
      By Rabs_def2 it holds that (b N3 - l < ε ∧ - ε < b N3 - l).
      We conclude that (& b N3 < l + ε = l + (m - l)/2 
                            = m - (m - l)/2 = m - ε < a N3).
    }
    It holds that (a N3 <= b N3).
    Contradiction.
Qed.

Definition is_bounded (a : ℕ → ℝ) := 
  ∃ q : ℝ,
    ∃ M : ℝ, M > 0 ∧
      ∀ n : ℕ, 
        |a n - q| ≤ M.
Notation "a 'is' '_bounded_'" := (is_bounded a) (at level 20).
Notation "a 'is' 'bounded'" := (is_bounded a) (at level 20, only parsing).
Local Ltac2 unfold_is_bounded    ()          := unfold is_bounded.
Local Ltac2 unfold_is_bounded_in (h : ident) := unfold is_bounded in $h.
Ltac2 Notation "Expand" "the" "definition" "of" "bounded" cl(opt(seq("in", "(", ident, ")"))) := 
  expand_def_framework unfold_is_bounded unfold_is_bounded_in cl.

Definition is_bounded_equivalent (a : ℕ → ℝ) :=
  ∃ M : ℝ, M > 0 ∧ 
    ∀ n : ℕ, |a n| ≤ M.
    
Lemma is_bounded_equivalence : 
  ∀ (a : ℕ → ℝ),
    is_bounded a ⇔ 
      is_bounded_equivalent a.
Proof.
Take a : (ℕ → ℝ).
We show both directions.
- We need to show that (is_bounded a ⇨ is_bounded_equivalent a).
  Assume that (is_bounded a).
  It holds that (there exists q : R, 
    there exists M1 : R, M1 > 0 ∧ (for all n : ℕ, | a n - q | ≤ M1)).
  Obtain such a q.
  It holds that (there exists M1 : R, M1 > 0 ∧ (for all n : ℕ, | a n - q | ≤ M1)).
  Obtain such an M1.
  It holds that (M1 > 0 ∧ (for all n : ℕ, | a n - q | ≤ M1)) (i).
  Because (i) both (M1 > 0) and 
    (for all n : ℕ, | a n - q | ≤ M1).
  We need to show that (
    there exists M : ℝ ,
      M > 0 ∧ (for all n : ℕ,
        | a n | ≤ M)).
  Choose M := (M1 + |q|).
  We show both statements.
  + We need to show that (M > 0).
    It holds that (0 ≤ |q|).
    It suffices to show that (0 <= M).
    We conclude that (& 0 <= (M1 + |q|) = M).

  + We need to show that (
      for all n : ℕ,
        | a n | ≤ M ).
    Take n : ℕ.
    By Rabs_triang it holds that (|a n - q + q| ≤ |a n - q| + |q|).
    We conclude that (& |a n| = |a n - q + q| 
                              <= (|a n - q| + |q|) <= (M1 + |q|) = M).

- We need to show that (
    is_bounded_equivalent a ⇨ is_bounded a).
  Assume that (there exists M1 : ℝ, M1 > 0 ∧ ∀ n : ℕ, |a n| ≤ M1).
  Obtain such an M1. It holds that 
    (M1 > 0 ∧ ∀ n : ℕ, |a n| ≤ M1) (i).
  Because (i) both (M1 > 0) and
  (for all n : ℕ, | a n | ≤ M1) hold.
  (* Expand the definition of is_bounded. *)
  We need to show that (
there exists q M : ℝ ,
M > 0 ∧ (for all n : ℕ,
| a n - q | ≤ M)
).
  Choose q := 0.
  Choose M := M1.
  We show both statements.
  + We need to show that (M > 0).
    It follows that (M > 0).
  + We need to show that (
for all n : ℕ,
| a n - q | ≤ M ).
  Take n : ℕ.
  We conclude that (& |a n - q| = |a n| <= M).
Qed.

(** Definitions sequence bounded from above and below *)
Definition is_bounded_above (a : ℕ → ℝ) := 
  ∃ M : ℝ, ∀ n : ℕ, a(n) ≤ M.
Notation "a 'is' '_bounded' 'above_'" := (is_bounded_above a) (at level 20).
Notation "a 'is' 'bounded' 'above'" := (is_bounded_above a) (at level 20, only parsing).
Local Ltac2 unfold_is_bounded_above    ()          := unfold is_bounded_above.
Local Ltac2 unfold_is_bounded_above_in (h : ident) := unfold is_bounded_above in $h.
Ltac2 Notation "Expand" "the" "definition" "of" "bounded" "above" cl(opt(seq("in", "(", ident, ")"))) := 
  expand_def_framework unfold_is_bounded_above unfold_is_bounded_above_in cl.

Definition is_bounded_below (a : ℕ → ℝ) :=
  ∃ m : ℝ, ∀ n : ℕ, m ≤ a(n).
Notation "a 'is' '_bounded' 'below_'" := (is_bounded_below a) (at level 20).
Notation "a 'is' 'bounded' 'below'" := (is_bounded_below a) (at level 20, only parsing).
Local Ltac2 unfold_is_bounded_below    ()          := unfold is_bounded_below.
Local Ltac2 unfold_is_bounded_below_in (h : ident) := unfold is_bounded_below in $h.
Ltac2 Notation "Expand" "the" "definition" "of" "bounded" "below" cl(opt(seq("in", "(", ident, ")"))) := 
  expand_def_framework unfold_is_bounded_below unfold_is_bounded_below_in cl.


(** Convergence to +∞ and -∞. *)
Definition diverges_to_plus_infinity (a : ℕ → ℝ) := 
  ∀ M : ℝ,
    ∃ N : ℕ,
      ∀ n : ℕ, (n ≥ N)%nat ⇒
        a(n) ≥ M.

Notation "a ⟶ ∞" := (diverges_to_plus_infinity a) (at level 20).
Notation "a '_diverges' 'to' '∞_'" := (diverges_to_plus_infinity a) (at level 20).
Notation "a 'diverges' 'to' '∞'"   := (diverges_to_plus_infinity a) (at level 20, only parsing).
Local Ltac2 unfold_diverge_plus_infty ()             := unfold diverges_to_plus_infinity.
Local Ltac2 unfold_diverge_plus_infty_in (h : ident) := unfold diverges_to_plus_infinity in $h.
Ltac2 Notation "Expand" "the" "definition" "of" "⟶" "∞" cl(opt(seq("in", "(", ident, ")"))) := 
  expand_def_framework unfold_diverge_plus_infty unfold_diverge_plus_infty_in cl.
Ltac2 Notation "Expand" "the" "definition" "of" "diverges" "to" "∞" cl(opt(seq("in", "(", ident, ")"))) := 
  expand_def_framework unfold_diverge_plus_infty unfold_diverge_plus_infty_in cl.

Definition diverges_to_minus_infinity (a : ℕ → ℝ) := 
  ∀ M : ℝ,
    ∃ N : ℕ,
      ∀ n : ℕ, (n ≥ N)%nat ⇒
        a(n) ≤ M.

Notation "a ⟶ -∞" := (diverges_to_minus_infinity a) (at level 20).
Notation "a '_diverges' 'to' '-∞_'" := (diverges_to_minus_infinity a) (at level 20).
Notation "a 'diverges' 'to' '-∞'"   := (diverges_to_minus_infinity a) (at level 20, only parsing).
Local Ltac2 unfold_diverge_minus_infty ()             := unfold diverges_to_minus_infinity.
Local Ltac2 unfold_diverge_minus_infty_in (h : ident) := unfold diverges_to_minus_infinity in $h.
Ltac2 Notation "Expand" "the" "definition" "of" "⟶" "-∞" cl(opt(seq("in", "(", ident, ")"))) := 
  expand_def_framework unfold_diverge_minus_infty unfold_diverge_minus_infty_in cl.
Ltac2 Notation "Expand" "the" "definition" "of" "diverges" "to" "-∞" cl(opt(seq("in", "(", ident, ")"))) := 
  expand_def_framework unfold_diverge_minus_infty unfold_diverge_minus_infty_in cl.

Close Scope R_scope.
