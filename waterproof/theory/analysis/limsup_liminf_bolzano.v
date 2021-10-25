(** * Lim sup, lim inf and Bolzano-Weierstrass

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

Require Import Waterproof.AllTactics.
Require Import Waterproof.load_database.RealsAndIntegers.
Require Import Waterproof.notations.notations.
Require Import Waterproof.set_search_depth.To_5.
Require Import Waterproof.set_intuition.Disabled.
Require Import Waterproof.load_database.DisableWildcard.

Require Import Waterproof.theory.analysis.sequences.
Require Import Waterproof.theory.analysis.subsequences.
Require Import Waterproof.theory.analysis.sup_and_inf.
Require Import Waterproof.theory.analysis.sequential_accumulation_points.

Global Hint Resolve Rabs_Rabsolu.
(** ## lim sup*)
Definition lim_sup_bdd (a : ℕ → ℝ) 
                       (pr1 : has_ub a) 
                       (pr2 : has_lb (sequence_ub a pr1)) :=
  decreasing_cv (sequence_ub a pr1)
                (Wn_decreasing a pr1)
                (pr2).

Lemma lim_const_min_1_over_n_plus_1 :
  ∀ x : ℝ, Un_cv (fun (n : ℕ) ↦ x - 1 / (INR n + 1)) x.
Proof.
Take x : ℝ.
    It holds that H1 : (x = x - 0).
    rewrite H1 at 1.
    apply CV_minus with
      (An := fun (n : ℕ) ↦ x)
      (Bn := fun (n : ℕ) ↦ 1 / (INR n + 1))
      (l1 := x)
      (l2 := 0).
    Apply lim_const_seq.
    Apply lim_d_0.
Qed.

Lemma exists_almost_lim_sup : 
  ∀ (a : ℕ → ℝ) (pr1 : has_ub a) (pr2 : has_lb (sequence_ub a pr1)) (m : ℕ) (N : ℕ),
    ∃ k : ℕ, (N ≤ k)%nat ∧ a k > proj1_sig (lim_sup_bdd a pr1 pr2) - 1 / (INR(m) + 1).
Proof.
    Take a : (ℕ → ℝ). 
    Take pr1 : (has_ub a). 
    Take pr2 : (has_lb (sequence_ub a pr1)). 
    Take m Nn : ℕ.
    By exists_almost_lim_sup_aux it holds that H1 : (∃ k : ℕ, (k ≥ Nn)%nat ∧ a k > sequence_ub a pr1 Nn - 1 / (INR(m) + 1)).
    Choose n such that n_good according to H1.
    Choose k := n.
    We show both statements.
    - We need to show that (Nn ≤ k)%nat.
      This follows immediately.
    - We need to show that (a k > proj1_sig (lim_sup_bdd a pr1 pr2) - 1 / (m + 1)).
      We claim that H2 : (proj1_sig (lim_sup_bdd a pr1 pr2) ≤ sequence_ub a pr1 Nn).
      Expand the definition of lim_sup_bdd.
      That is, write the goal as 
        (proj1_sig (decreasing_cv (sequence_ub a pr1) (Wn_decreasing a pr1) pr2) 
          ≤ sequence_ub a pr1 Nn).
      Define lim_with_proof := (decreasing_cv (sequence_ub a pr1) (Wn_decreasing a pr1) pr2).
      Choose l such that l_is_lim according to lim_with_proof.
      Simplify what we need to show. 
      We need to show that (l ≤ sequence_ub a pr1 Nn).
      By Wn_decreasing it holds that H3 : (Un_decreasing (sequence_ub a pr1)).
      apply decreasing_ineq with (Un := (sequence_ub a pr1)) (l := l) (n := Nn).
      This follows by assumption.
      This follows immediately.
      Because n_good both part1 and part2.
      It holds that H3 : (proj1_sig (lim_sup_bdd a pr1 pr2) - 1 / (m + 1) ≤ a n).
      Rewrite using (k = n).
      This concludes the proof.
Qed.


Lemma exists_subseq_to_limsup_bdd :
   ∀ (a : ℕ → ℝ) (pr1 : has_ub a) (pr2 : has_lb (sequence_ub a pr1)),
    ∃ n : ℕ → ℕ, is_index_seq n ∧ ∀ k : ℕ, a (n k) > proj1_sig (lim_sup_bdd a pr1 pr2) - 1 / (INR(k) + 1).
Proof.
    Take a : (ℕ → ℝ). 
    Take pr1 : (has_ub a). 
    Take pr2 : (has_lb (sequence_ub a pr1)).
    apply exists_good_subseq with (P := fun (m : ℕ) (y :ℝ) ↦ y > proj1_sig (lim_sup_bdd a pr1 pr2) - 1 / (INR(m) + 1) ).
    Apply exists_almost_lim_sup.
Qed.



Lemma sequence_ub_bds :
  ∀ (a : ℕ → ℝ) (pr : has_ub a) (N : ℕ) (n : ℕ),
    (n ≥ N)%nat ⇒ a n ≤ sequence_ub a pr N.
Proof.
    Take a : (ℕ → ℝ). 
    Take pr : (has_ub a).
    Take Nn n : ℕ.
    Assume n_ge_N : (n ≥ Nn)%nat.
    Expand the definition of sequence_ub.
    That is, write the goal as (a n ≤ lub (k) ↦ (a (Nn + k)%nat) (maj_ss a Nn pr)).
    Expand the definition of lub.
    That is, write the goal as
      (a n ≤ (let (a0, _) := ub_to_lub (k) ↦ (a (Nn + k)%nat) (maj_ss a Nn pr) in a0)).
    Define upp_bd_with_proof := (ub_to_lub (fun (k : ℕ) ↦ a (Nn +k)%nat)).
    Choose M such that M_is_sup according to upp_bd_with_proof.
    Expand the definition of is_lub in M_is_sup.
    That is, write M_is_sup as (is_upper_bound (EUn (k) ↦ (a (Nn + k)%nat)) M
      ∧ (for all b : ℝ, is_upper_bound (EUn (k) ↦ (a (Nn + k)%nat)) b ⇨ M ≤ b)).
    Because M_is_sup both M_is_upp_bd and any_upp_bd_ge_M.
    Expand the definition of is_upper_bound in M_is_upp_bd.
    That is, write M_is_upp_bd as (for all x : ℝ, EUn (k) ↦ (a (Nn + k)%nat) x ⇨ x ≤ M).
    It holds that H1 : (Nn + (n-Nn) = n)%nat.
    We claim that H2 : (EUn (fun (k : ℕ) ↦ (a (Nn + k)%nat)) (a n)).
    Expand the definition of EUn.
    That is, write the goal as (there exists i : ℕ, a n = a (Nn + i)%nat).
    We need to show that (∃ i : ℕ, a n = a (Nn + i)%nat).
    Choose i := (n - Nn)%nat.
    Rewrite using (n = (n - Nn) + Nn)%nat.
    Rewrite using (i = n - Nn)%nat.
    Rewrite using ((Nn + (n - Nn))%nat = (Nn + n - Nn)%nat).
    This concludes the proof.
    We need to show that (a n ≤ M).
    Apply M_is_upp_bd.
    Apply H2.
Qed.


(** ## A slightly upgraded version of the Bolzano-Weierstrass Theorem*)
Theorem Bolzano_Weierstrass_gen :
  ∀ (a : ℕ → ℝ) (pr_ub : has_ub a) (pr_lb : has_lb (sequence_ub a pr_ub)),
    ∃ (n : ℕ → ℕ), is_index_seq n ∧ Un_cv (fun (k : ℕ) ↦ a (n k)) (proj1_sig (lim_sup_bdd a pr_ub pr_lb)).
Proof.
    Take a : (ℕ → ℝ).
    Take pr_ub : (has_ub a).
    Take pr_lb : (has_lb (sequence_ub a pr_ub)).
    Define L_with_proof := (lim_sup_bdd a pr_ub pr_lb).
    Define L := (proj1_sig L_with_proof).
    Define sequence_ub_cv_to_L := (proj2_sig L_with_proof).
    We claim that H1 : (∃ m : ℕ → ℕ, is_index_seq m 
                ∧ 
     ∀ k : ℕ, 
      a (m k) > L - 1 / (INR(k) + 1)).
    {
      Choose m_seq such that m_seq_props according to (exists_subseq_to_limsup_bdd a pr_ub pr_lb).
      Because m_seq_props both m_seq_ind_seq and m_seq_prop_for_k.
      Choose m := m_seq.
      We show both statements.
      - We need to show that (is_index_seq m).
        We conclude that (is_index_seq m).
      - We need to show that (for all k : ℕ, a (m k) > L - 1 / (k + 1)).
        We conclude that (∀ k : ℕ, a (m k) > L - 1 / (INR(k) + 1)).
    }
    Choose m such that m_props according to H1.
    Because m_props both m_ind_seq and amk_large.
    Choose n := m.
    We need to show that (is_index_seq m ∧ Un_cv (k) ↦ (a (m k)) L).
    We show both statements.
    - We need to show that (is_index_seq m).
      By m_ind_seq we conclude that (is_index_seq n).
    - We need to show that (Un_cv (k) ↦ (a (n k)) L).
      (** TODO: an equivalent to "apply with" would be nice here *)
      Apply (squeeze_theorem (fun (k : ℕ) ↦ L - 1 / (INR k + 1)) 
        (fun (k : ℕ) ↦ (a (n k)))
        (sequence_ub a pr_ub)).
      + (* apply squeeze_theorem with (c := sequence_ub a pr_ub)
        (a := fun (k : ℕ) ↦ L - 1 / (INR k + 1)).*)
        Take k : ℕ.
        We show both statements.
        * We need to show that (L - 1 / (k + 1) ≤ a (n k)).
          By amk_large it holds that amk_large_spec : (a (m k) > L - 1 / (k+1)).
          We conclude that (L - 1 / (k + 1) ≤ a (n k)).
        * We need to show that (a (n k) ≤ sequence_ub a pr_ub k).
          By index_seq_grows_0 it holds that H1 : (m k ≥ k)%nat.
          Apply sequence_ub_bds; assumption.
      + Apply lim_const_min_1_over_n_plus_1.
      + Apply sequence_ub_cv_to_L.
Qed.

(** ## The Bolzano-Weierstrass Theorem*)
Theorem Bolzano_Weierstrass :
  ∀ (a : ℕ → ℝ), has_ub a ⇒ (has_lb a ⇒ 
    ∃ (n : ℕ → ℕ) (l : ℝ), is_index_seq n ∧
      Un_cv (fun (k : ℕ) ↦ a (n k)) l ).
Proof.
    Take a : (ℕ → ℝ).
    Take pr_ub : (has_ub a).
    Take pr_lb : (has_lb a).
    Define pr2 := (maj_min a pr_ub pr_lb).
    We claim that H :
      (∃ (n : ℕ → ℕ), is_index_seq n
        ∧ Un_cv (fun (k : ℕ) ↦ a (n k)) (proj1_sig (lim_sup_bdd a pr_ub pr2))).
    Apply (Bolzano_Weierstrass_gen a pr_ub pr2).
    Choose n0 such that n_good_subseq according to H.
    Choose n := n0.
    Choose l := (proj1_sig (lim_sup_bdd a pr_ub pr2)).
    We conclude that (is_index_seq n ∧ Un_cv (k) ↦ (a (n k)) (proj1_sig (lim_sup_bdd a pr_ub pr2))).
Qed.

Lemma acc_pt_bds_seq_ub :
  ∀ (a : ℕ → ℝ) (pr_ub : has_ub a) (x : ℝ),
    is_seq_acc_pt a x ⇒ ∀ m : ℕ, x ≤ sequence_ub a pr_ub m.
Proof.
    Take a : (ℕ → ℝ).
    Take pr_ub : (has_ub a).
    Take x : ℝ.
    Assume x_is_acc_pt : (is_seq_acc_pt a x).
    Expand the definition of is_seq_acc_pt in x_is_acc_pt.
    That is, write x_is_acc_pt as (there exists n : ℕ ⇨ ℕ, is_index_seq n 
      ∧ Un_cv (k) ↦ (a (n k)) x).
    Choose n such that n_good_ind_seq according to x_is_acc_pt.
    Because n_good_ind_seq both n_ind_seq and ank_cv_to_x.
    Take m : ℕ.
    Define L := (sequence_ub a pr_ub m).
    By Rle_or_lt it holds that H : (x ≤ L ∨ L < x).
    Because H either x_le_L or L_lt_x.
    Case ( x ≤ L ).
    We conclude that (x ≤ L).
    Case ( L < x ).
    Define ε := (x - L).
    We claim that H1 : (∃ K : ℕ, ∀ k : ℕ, (k ≥ K)%nat ⇒ R_dist (a (n k)) x < ε).
    Apply ank_cv_to_x.
    It holds that H2 : (x - L > 0).
    It follows that (ε > 0).
    Choose K such that ank_close_to_x according to H1.
    Define Nn := (Nat.max K m).
    We claim that H6 : (R_dist (a (n Nn)) x < ε).
    Apply ank_close_to_x.
    It holds that H7 : (Nat.max K m ≥ K)%nat.
    It follows that (Nn ≥ K)%nat.
    Expand the definition of R_dist in H6.
    That is, write H6 as ( | a (n Nn) - x | < ε ).
    By Rabs_def2 it holds that H8 : (a(n Nn) - x < ε ∧ - ε < a(n Nn) - x).
    Because H8 both H9 and H10.
    By index_seq_grows_0 it holds that H14 : (n Nn ≥ Nn)%nat.
    We claim that H15 : (a (n Nn) ≤ L).
    Apply sequence_ub_bds.
    It holds that H16 : (Nat.max K m ≥ m)%nat.
    It follows that (n Nn ≥ m)%nat.
    Rewrite using (ε = x - L) in H10.
    It follows that (x ≤ L).
Qed.

(** ## Comparing definitions of lim sup*)
Lemma lim_sup_bdd_is_sup_seq_acc_pts :
  ∀ (a : ℕ → ℝ) (pr_ub : has_ub a) (pr_lb : has_lb (sequence_ub a pr_ub)),
    is_sup (is_seq_acc_pt a) (proj1_sig (lim_sup_bdd a pr_ub pr_lb)).
Proof.
    Take a : (ℕ → ℝ).
    Take pr_ub : (has_ub a).
    Take pr_lb : (has_lb (sequence_ub a pr_ub)).
    (* TODO: fix that we refer to is_lub here. Moreover, we show both statements should work immediately. *)
    Expand the definition of is_lub.
    That is, write the goal as 
      (is_upper_bound (is_seq_acc_pt a) (proj1_sig (lim_sup_bdd a pr_ub pr_lb))
      ∧ (for all b : ℝ, is_upper_bound (is_seq_acc_pt a) b ⇨ proj1_sig (lim_sup_bdd a pr_ub pr_lb) ≤ b)).
    We show both statements.
    - We need to show that (is_upper_bound (is_seq_acc_pt a) (proj1_sig (lim_sup_bdd a pr_ub pr_lb))).
      Expand the definition of is_upper_bound.
      That is, write the goal as (for all x : ℝ, is_seq_acc_pt a x ⇨ x ≤ proj1_sig (lim_sup_bdd a pr_ub pr_lb)).
      Take x : ℝ.
      Assume x_is_acc_pt : (is_seq_acc_pt a x).
      By acc_pt_bds_seq_ub it holds that H0 : (∀ m : ℕ, x ≤ sequence_ub a pr_ub m).
      Define L_with_proof := (lim_sup_bdd a pr_ub pr_lb).
      Choose L such that sequence_ub_cv_to_L according to L_with_proof.
      (* TODO: fix *)
      simpl.
      By (low_bd_seq_is_low_bd_lim (sequence_ub a pr_ub))
          it holds that H1 : (L ≥ x).
      We conclude that (x ≤ L).
    - We need to show that (for all b : ℝ, is_upper_bound (is_seq_acc_pt a) b 
        ⇨ proj1_sig (lim_sup_bdd a pr_ub pr_lb) ≤ b).
      Take b : ℝ.
      Assume b_upp_bd : (is_upper_bound (is_seq_acc_pt a) b).
      Expand the definition of is_upper_bound in b_upp_bd.
      That is, write b_upp_bd as (for all x : ℝ, is_seq_acc_pt a x ⇨ x ≤ b).
      Expand the definition of is_seq_acc_pt in b_upp_bd.
      That is, write b_upp_bd as (for all x : ℝ, 
        (there exists n : ℕ ⇨ ℕ, is_index_seq n ∧ Un_cv (k) ↦ (a (n k)) x) ⇨ x ≤ b).
      Apply b_upp_bd.
      Apply Bolzano_Weierstrass_gen.
Qed.

(** ## Some attempts to get nicer subsequences*)
(** In a sequence, either there are finitely many terms larger than or equal to a given number $L$, or for every $N$ there is an $n \geq N$ such that $a_n \geq L$.*)
Lemma finite_or_find_one :
  ∀ (a : ℕ → ℝ) (L : ℝ),
    (∃ N : ℕ, ∀ k : ℕ, (k >= N)%nat ⇒ a k < L) 
       ∨ 
    (∀ m : ℕ, ∃ n : ℕ, (n >= m)%nat ∧ a n ≥ L).
Proof.
    Take a : (ℕ → ℝ).
    Take L : ℝ. 
    Define P := (∃ N : ℕ, ∀ k : ℕ, (k >= N)%nat ⇒ a k < L).
    (** TODO: fix *)
    destruct (classic P).
    We conclude that (P  ∨ (for all m : ℕ,
       there exists n : ℕ ,
         (n ≥ m)%nat ∧ a n ≥ L)).
    (** TODO: fix *)
    (** It is enough to show the proposition of the *)
    right
    (** hand side of the or-sign*)
    .

    Take m : ℕ.
    We claim that H0 : (∀ Nn : ℕ, ¬(∀ k : ℕ, (k >= Nn)%nat ⇒ a k < L)).
    Apply not_ex_all_not.
    Apply H.
    
    (* By not_ex_all_not it holds that H0 : (∀ Nn : ℕ, ¬(∀ k : ℕ, (k >= Nn)%nat ⇒ a k < L)). *)
    (* Expand the definition of P in H. *)
    It holds that H1 : (¬(∀ k : ℕ, (k >= m)%nat ⇒ a k < L)).
    By not_all_ex_not it holds that H2 : (∃ n : ℕ, ¬((n >= m)%nat ⇒ a n < L)).
    Choose n1 such that H3 according to H2.
    Choose n := n1.
    By imply_to_and it holds that H4 : ((n1 ≥ m)%nat ∧ ¬(a n1 < L) ).
    Because H4 both H5 and H6.
    We show both statements.
    - We need to show that (n ≥ m)%nat.
      By H5 we conclude that (n ≥ m)%nat.
    - We need to show that (a n ≥ L).
      By H6 it holds that H7: (a n1 ≥ L).
      We conclude that (a n ≥ L).
Qed.