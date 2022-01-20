(** # Sequential accumulation points*)
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

Require Import Waterproof.theory.analysis.sequences.
Require Import Waterproof.theory.analysis.subsequences.

Global Hint Resolve Rabs_Rabsolu.

Definition is_seq_acc_pt (a : ℕ → ℝ) (x : ℝ) : Prop :=
  ∃ n : ℕ → ℕ, is_index_seq n ∧ Un_cv (fun (k : ℕ) ↦ a(n k)) x.


Lemma seq_bdd_seq_acc_pts_bdd :
  ∀ a : ℕ → ℝ, has_ub a ⇒ bound (is_seq_acc_pt a).
Proof.
    Take a : (ℕ → ℝ).
    Assume that (has_ub a) (i).
    Expand the definition of bound.
    That is, write the goal as 
      (there exists m : ℝ, is_upper_bound (is_seq_acc_pt a) m).
    Expand the definition of is_upper_bound.
    That is, write the goal as (there exists m : ℝ,
      for all x : ℝ, is_seq_acc_pt a x ⇨ x ≤ m).
    Choose M according to (i), so for M : R it holds that
      (is_upper_bound (EUn a) M) (ii).
    Choose m := M.
    Take x : ℝ.
    Assume that (is_seq_acc_pt a x) (iii).
    Expand the definition of is_seq_acc_pt in (iii).
    That is, write (iii) as (there exists n : ℕ ⇨ ℕ,
      is_index_seq n ∧ Un_cv (k) ↦ (a (n k)) x).
    Choose n according to (iii), so for n : ℕ → ℕ it holds that
      (is_index_seq n ∧ Un_cv (k) ↦ (a (n k)) x) (iv).
    Because (iv) both (is_index_seq n) and (Un_cv (k) ↦ (a (n k)) x) hold.
    We need to show that (x ≤ M).
    By upp_bd_seq_is_upp_bd_lim it suffices to show that (for all k : nat, (a (n k) <= M)).
    Expand the definition of is_upper_bound in (ii).
    That is, write (ii) as (for all x0 : ℝ, EUn a x0 ⇨ x0 ≤ M).
    Expand the definition of EUn in (ii).
    That is, write (ii) as (for all x0 : ℝ, 
      (there exists k : ℕ, x0 = a k) ⇨ x0 ≤ M).
    We claim that (for all k : ℕ, (a k) ≤ M) (v).
    { Take k : ℕ.
      It suffices to show that (there exists k0 : nat, a k = a k0).
      Choose k0 := k.
      We conclude that (a k = a k0).
    }
    Take n0 : ℕ.
    By (i) it holds that (a(n n0) ≤ M).
    It follows that (a(n n0) ≤ M).
Qed.
