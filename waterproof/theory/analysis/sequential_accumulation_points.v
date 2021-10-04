(** # Sequential accumulation points*)
Require Import Reals.
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

Require Import Waterproof.theory.analysis.sequences.
Require Import Waterproof.theory.analysis.subsequences.

Global Hint Resolve Rabs_Rabsolu.

Definition is_seq_acc_pt (a : ℕ → ℝ) (x : ℝ) : Prop :=
  ∃ n : ℕ → ℕ, is_index_seq n ∧ Un_cv (fun (k : ℕ) ↦ a(n k)) x.


Lemma seq_bdd_seq_acc_pts_bdd :
  ∀ a : ℕ → ℝ, has_ub a ⇒ bound (is_seq_acc_pt a).
Proof.
    Take a : (ℕ → ℝ).
    Assume a_upp_bdd : (has_ub a).
    Expand the definition of bound.
    Expand the definition of is_upper_bound.
    Choose M such that a_bdd_by_M according to a_upp_bdd.
    Choose m := M.
    Take x : ℝ.
    Assume x_is_acc_pt : (is_seq_acc_pt a x).
    Expand the definition of is_seq_acc_pt.
    Choose n such that n_good_ind_seq according to x_is_acc_pt.
    Because n_good_ind_seq both n_ind_seq and subseq_conv_to_x.
    We need to show that (x ≤ M).
    Apply (upp_bd_seq_is_upp_bd_lim (fun (k : ℕ)↦ a(n k))).
    Expand the definition of is_upper_bound in a_bdd_by_M.
    Expand the definition of EUn in a_bdd_by_M.
    We claim that H : (for all i : ℕ, (a i) ≤ M).
    Take i : ℕ.
    Apply (a_bdd_by_M (a i)).
    Choose i0 := i.
    This follows by reflexivity.
    Take n0 : ℕ.
    By H it holds that H2 : (a(n n0) ≤ M).
    It follows that (a(n n0) ≤ M).
    Apply subseq_conv_to_x.
Qed.
