(* Validation: all *example* proofs from waterproof_tutorial_fr.mv, in French. *)
From Stdlib Require Import Rbase.
From Stdlib Require Import Rfunctions.

Require Import Waterproof.Notations.Common.
Require Import Waterproof.Notations.Reals.
Require Import Waterproof.Notations.Sets.
Require Import Waterproof.Chains.
Require Import Waterproof.French.
Require Import Waterproof.Libs.Analysis.SupAndInf.
Require Import Waterproof.Automation.

Waterproof Enable Automation RealsAndIntegers.
Waterproof Language French.

Open Scope R_scope.
Open Scope subset_scope.

Notation "'max(' x , y )" := (Rmax x y) (format "'max(' x ,  y ')'").
Notation "'min(' x , y )" := (Rmin x y) (format "'min(' x ,  y ')'").

Lemma example_reflexivity : 0 = 0.
Proof. Nous concluons que 0 = 0. Qed.

Lemma example_we_need_to_show_that : 2 = 2.
Proof. Nous devons montrer que 2 = 2. Nous concluons que 2 = 2. Qed.

Lemma example_take : ∀ x ∈ ℝ, x = x.
Proof. Soit x ∈ ℝ. Nous concluons que x = x. Qed.

Lemma example_choose : ∃ y ∈ ℝ, y < 3.
Proof. Choisissons y := 2. { En effet, y ∈ ℝ. } Nous concluons que y < 3. Qed.

Lemma example_combine_quantifiers : ∀ a ∈ ℝ, ∀ b > 5, ∃ c ∈ ℝ, c > b - a.
Proof.
Soit a ∈ ℝ. Soit b > 5. Choisissons c := b - a + 1.
{ En effet, c ∈ ℝ. } Nous concluons que c > b - a.
Qed.

Lemma example_assumptions : ∀ a ∈ ℝ, a < 0 ⇒ - a > 0.
Proof. Soit a ∈ ℝ. Supposons que a < 0. Nous concluons que - a > 0. Qed.

Lemma example_assumptions_2 : ∀ a ∈ ℝ, a < 0 ⇒ - a > 0.
Proof. Soit a ∈ ℝ. Supposons que a < 0 as (i). Par (i) nous concluons que - a > 0. Qed.

Section monotone_function.
Variable f : ℝ → ℝ.
Parameter f_increasing : ∀ x ∈ ℝ, ∀ y ∈ ℝ, x ≤ y ⇒ f(x) ≤ f(y).

Lemma example_inequalities: 2 < f(0) ⇒ 2 < f(1).
Proof. Supposons que 2 < f(0). Par f_increasing nous concluons que & 2 < f(0) ≤ f(1). Qed.

Lemma example_backwards : 3 < f(0) ⇒ 2 < f(5).
Proof.
Supposons que 3 < f(0). Il suffit de montrer que f(0) ≤ f(5).
Par f_increasing nous concluons que f(0) ≤ f(5).
Qed.

Lemma example_forwards : 7 < f(-1) ⇒ 2 < f(6).
Proof.
Supposons que 7 < f(-1). Par f_increasing il s'avère que f(-1) ≤ f(6).
Nous concluons que 2 < f(6).
Qed.
End monotone_function.

Lemma example_use_for_all : ∀ x ∈ ℝ, (∀ ε > 0, x < ε) ⇒ x + 1/2 < 1.
Proof.
Soit x ∈ ℝ. Supposons que ∀ ε > 0, x < ε as (i).
Utilisons ε := 1/2 dans (i). { En effet, 1 / 2 > 0. }
Il s'avère que  x < 1 / 2. Nous concluons que x + 1/2 < 1.
Qed.

Lemma example_use_there_exists : ∀ x ∈ ℝ, (∃ y > 10, y < x) ⇒ 10 < x.
Proof.
Soit x ∈ ℝ. Supposons que ∃ y > 10, y < x as (i). Obtenons un tel y.
Nous concluons que & 10 < y < x.
Qed.

Lemma example_use_there_exists_2 : ∀ x ∈ ℝ, (∃ y > 14, y < x) ⇒ 12 < x.
Proof.
Soit x ∈ ℝ. Supposons que ∃ y > 14, y < x as (i). Obtenons y à partir de (i).
Nous concluons que & 12 < y < x.
Qed.

Lemma example_contradicition : ∀ x ∈ ℝ, (∀ ε > 0, x > 1 - ε) ⇒ x ≥ 1.
Proof.
Soit x ∈ ℝ. Supposons que ∀ ε > 0, x > 1 - ε as (i).
Nous devons montrer que x ≥ 1. Raisonnons par l'absurde.
Supposons que ¬ (x ≥ 1). Il s'avère que (1 - x) > 0.
Par (i) il s'avère que x > 1 - (1 - x). Contradiction.
Qed.

Lemma example_cases : ∀ x ∈ ℝ, ∀ y ∈ ℝ, max(x, y) = x ∨ max(x, y) = y.
Proof.
Soit x ∈ (ℝ). Soit y ∈ (ℝ). Ou bien x < y ou bien x ≥ y.
- Cas x < y. Il suffit de montrer que max(x, y) = y. Nous concluons que max(x, y) = y.
- Cas x ≥ y. Il suffit de montrer que max(x, y) = x. Nous concluons que max(x, y) = x.
Qed.

Lemma example_both_statements : ∀ x ∈ ℝ, x^2 ≥ 0 ∧ | x | ≥ 0.
Proof.
Soit x ∈ ℝ. Prouvons les deux énoncés.
* Nous devons montrer que x^2 ≥ 0. Nous concluons que x^2 ≥ 0.
* Nous devons montrer que | x | ≥ 0. Nous concluons que | x | ≥  0.
Qed.

Lemma example_both_directions : ∀ x ∈ ℝ, ∀ y ∈ ℝ, x < y ⇔ y > x.
Proof.
Soit x ∈ ℝ. Soit y ∈ ℝ. Prouvons les deux sens.
++ Nous devons montrer que x < y ⇒ y > x. Supposons que x < y. Nous concluons que y > x.
++ Nous devons montrer que y > x ⇒ x < y. Supposons que y > x. Nous concluons que x < y.
Qed.

Lemma example_induction :
  ∀ n : ℕ → ℕ, (∀ k ∈ ℕ, (n(k) < n(k+1))%nat) ⇒ ∀ k ∈ ℕ, (k ≤ n(k))%nat.
Proof.
Soit n : ℕ → ℕ. Supposons que (∀ k ∈ ℕ, n(k) < n(k+1))%nat.
Raisonnons par récurrence sur k.
+ Traitons d'abord le cas de base (0 ≤ n(0))%nat. Nous concluons que (0 ≤ n(0))%nat.
+ Traitons maintenant l'étape de récurrence.
  Soit k ∈ ℕ. Supposons que (k ≤ n(k))%nat.
  Il s'avère que (n(k) < n(k+1))%nat. Il s'avère que (n(k) + 1 ≤ n(k+1))%nat.
  Nous concluons que (& k + 1 ≤ n(k) + 1 ≤ n(k + 1))%nat.
Qed.

Definition square (x : ℝ) := x^2.
Waterproof Register Expand "square"; for square; as "Definition square".

(* NB: Développons/Développons tout deliberately throw a "remove this line"
   reminder (like English Expand/Expand All), so they are omitted here. *)
Lemma example_expand : ∀ x ∈ ℝ, square x ≥ 0.
Proof.
Soit x ∈ (ℝ).
Nous devons montrer que x^2 ≥ 0. Nous concluons que x^2 ≥ 0.
Qed.
