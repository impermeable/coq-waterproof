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

Require Import Automation.
Require Import Libs.Analysis.Sequences.
Require Import Libs.Analysis.Subsequences.
Require Import Libs.Analysis.SupAndInf.
Require Import Libs.Analysis.SequentialAccumulationPoints.
Require Import Notations.Common.
Require Import Notations.Reals.
Require Import Notations.Sets.
Require Import Chains.
Require Import Tactics.

Waterproof Enable Automation RealsAndIntegers.

Open Scope R_scope.

(** ## lim sup*)
Definition lim_sup_bdd (a : ℕ → ℝ)
                       (pr1 : has_ub a)
                       (pr2 : has_lb (sequence_ub a pr1))
                      : {l : ℝ | converges_to(sequence_ub(a, pr1), l)}.
Proof.
set (H := decreasing_cv (sequence_ub a pr1) (Wn_decreasing a pr1) (pr2)).
destruct H as [l wl].
exists l.
apply convergence_equivalence; assumption.
Defined.

Lemma lim_const_min_1_over_n_plus_1 (x : ℝ) :
  converges_to (fun (n : ℕ) ↦ x - 1 / (INR n + 1)) x.
Proof.
    It holds that (x = x - 0) (i).
    rewrite (i) at 1.
    apply convergence_minus with
      (a := fun (n : ℕ) ↦ x)
      (b := fun (n : ℕ) ↦ 1 / (INR n + 1))
      (m := x)
      (l := 0).
    - We need to show that ((constant_sequence x) ⟶ x).
      By lim_const_seq we conclude that ((constant_sequence x) ⟶ x).
    - We need to show that (converges_to d 0).
      By lim_d_0 we conclude that (converges_to d 0).
Qed.

Lemma exists_almost_lim_sup (a : ℕ → ℝ) (i : has_ub a) (ii : has_lb (sequence_ub a (i))) (m : ℕ) (N₀ : ℕ) :
    ∃ k : ℕ, (N₀ ≤ k)%nat ∧ a k > proj1_sig(_,_,lim_sup_bdd a (i) (ii)) - 1 / (INR(m) + 1).
Proof.
    By exists_almost_lim_sup_aux it holds that
      (∃ n : ℕ, (n ≥ N₀)%nat ∧ a n > sequence_ub a (i) N₀ - 1 / (INR(m) + 1)).
    Obtain such an n. It holds that
      ((n ≥ N₀)%nat ∧ a n > sequence_ub a (i) N₀ - 1 / (INR(m) + 1)) (iii).
    Choose k := n.
    We show both statements.
    - We need to show that (N₀ ≤ k)%nat.
      We conclude that (N₀ <= k)%nat.
    - We need to show that (a k > proj1_sig(_,_,lim_sup_bdd a (i) (ii)) - 1 / (m + 1)).
      We claim that (proj1_sig(_,_,lim_sup_bdd a (i) (ii)) ≤ sequence_ub a (i) N₀).
      { destruct (lim_sup_bdd a (i) (ii)).
        simpl.
        By Wn_decreasing it holds that (Un_decreasing (sequence_ub a (i))).
        apply decreasing_ineq.
        * assumption.
        * apply convergence_equivalence; assumption.
      }
      Because (iii) both (n ≥ N₀)%nat and
        (a n > sequence_ub a i N₀ - 1 / (m + 1)) hold.
      It holds that (proj1_sig(_, _, lim_sup_bdd a (i) (ii)) - 1 / (m + 1) ≤ a n) (v).
      We need to show that (proj1_sig(_, _, lim_sup_bdd a (i) (ii)) - 1 / (m + 1) < a k).
      We conclude that (& proj1_sig(_, _, lim_sup_bdd a (i) (ii)) - 1 / (m + 1) < a n = a k).
Qed.

Lemma exists_subseq_to_limsup_bdd (a : ℕ → ℝ) (i : has_ub a) (ii : has_lb (sequence_ub a (i))) :
    ∃ n : ℕ → ℕ, is_index_seq n ∧ ∀ k : ℕ, a (n k) > proj1_sig(_, _, lim_sup_bdd a (i) (ii)) - 1 / (INR(k) + 1).
Proof.
  (* TODO: notation for apply with parameters *)
  apply exists_good_subseq with (P := fun (m : ℕ) (y :ℝ) ↦ y > proj1_sig(_, _, lim_sup_bdd a (i) (ii)) - 1 / (INR(m) + 1) ).
  Take m, N₀ : nat.
  By exists_almost_lim_sup we conclude that (there exists k : ℕ, (N₀ ≤ k)%nat
    ∧ a k > proj1_sig(_, _, lim_sup_bdd a (i) (ii)) - 1 / (m + 1)).
Qed.

Lemma sequence_ub_bds (a : ℕ → ℝ) (i : has_ub a) (N₀ : ℕ) (n : ℕ) :
    (n ≥ N₀)%nat ⇒ a n ≤ sequence_ub a (i) N₀.
Proof.
    Assume that (n ≥ N₀)%nat.
    We need to show that (a n ≤ lub (fun k ↦ (a (N₀ + k)%nat), maj_ss a N₀ (i))).
    We need to show that
      (a n ≤ (let (a0, _) := ub_to_lub (fun k ↦ (a (N₀ + k)%nat), maj_ss a N₀ (i)) in a0)).
    Define ii := (ub_to_lub (fun (k : ℕ) ↦ a (N₀ +k)%nat) (maj_ss a N₀ (i))).
    We need to show that (a(n) ≤ (let (a0, _) := ii in a0)).
    clear _defeq.
    Obtain such an l. It holds that
      (is_lub (EUn (fun (k : ℕ) ↦ a (N₀ +k)%nat)) l).
    It holds that (Raxioms.is_upper_bound (EUn (fun k ↦ (a (N₀ + k)%nat)), l)
      ∧ (for all b : ℝ, Raxioms.is_upper_bound (EUn (fun k ↦ (a (N₀ + k)%nat)), b) ⇨ l ≤ b)) (iii).
    Because (iii) both (Raxioms.is_upper_bound (EUn (fun k ↦ (a (N₀ + k)%nat)), l))
      and (for all b : ℝ, Raxioms.is_upper_bound (EUn (fun k ↦ (a (N₀ + k)%nat)), b) ⇨ l ≤ b) hold.
    It holds that (for all x : ℝ, EUn (fun k ↦ (a (N₀ + k)%nat), x) ⇨ x ≤ l).
    It holds that (N₀ + (n-N₀) = n)%nat.

    It suffices to show that (EUn (fun (k : ℕ) ↦ (a (N₀ + k)%nat)) (a n)).
    We need to show that (there exists k : ℕ, a n = a (N₀ + k)%nat).
    We need to show that (∃ k : ℕ, a n = a (N₀ + k)%nat).
    Choose k := (n - N₀)%nat.
    We conclude that (& a n = a (N₀ + n - N₀)%nat = a (N₀ + k)%nat).
Qed.

(** ## A slightly upgraded version of the Bolzano-Weierstrass Theorem*)
Theorem Bolzano_Weierstrass_gen (a : ℕ → ℝ) (i : has_ub a) (ii : has_lb (sequence_ub a (i))) :
    ∃ n : ℕ → ℕ, is_index_seq n ∧
      converges_to (fun (k : ℕ) ↦ a (n k)) (proj1_sig(_,_,lim_sup_bdd a (i) (ii))).
Proof.
    Define L_with_proof := (lim_sup_bdd a (i) (ii)).
    Define L := (proj1_sig L_with_proof).
    Define sequence_ub_cv_to_L := (proj2_sig L_with_proof).
    We claim that (∃ m : ℕ → ℕ, is_index_seq m
      ∧ ∀ k : ℕ, a (m k) > L - 1 / (INR(k) + 1)).
    {
      By exists_subseq_to_limsup_bdd it holds that
        (there exists m_seq : ℕ ⇨ ℕ, is_index_seq m_seq
          ∧ (for all k : ℕ, a (m_seq k) > proj1_sig(_,_,lim_sup_bdd a (i) (ii)) - 1 / (k + 1))).
      Obtain such an m_seq. It holds that
       (is_index_seq m_seq ∧
        (for all k : ℕ, a (m_seq k) > proj1_sig(_,_,lim_sup_bdd a i ii) - 1 / (k + 1))) (v).
      Because (v) both (is_index_seq m_seq) and
        (for all k : ℕ, a (m_seq k) > proj1_sig(_,_,lim_sup_bdd a (i) (ii)) - 1 / (k + 1)) (vi) hold.
      Choose m := m_seq.
      We show both statements.
      - We need to show that (is_index_seq m).
        We conclude that (is_index_seq m).
      - We need to show that (for all k : ℕ, a (m k) > L - 1 / (k + 1)).
        By (vi) we conclude that (∀ k : ℕ, a (m k) > L - 1 / (INR(k) + 1)).
    }
    Obtain such an m. It holds that
      (is_index_seq m ∧ (for all k : ℕ, a (m k) > L - 1 / (k + 1))) (iv).
    Because (iv) both (is_index_seq m) (v) and
      (for all k : ℕ, a (m k) > L - 1 / (k + 1)) (vi) hold.
    Choose n := m.
    - We need to show that (is_index_seq(n) ∧ (fun k : ℕ ↦ a(n(k))) ⟶ L).
      We show both statements.
      * We need to show that (is_index_seq m).
        It suffices to show that (is_index_seq n).
        By (v) we conclude that (is_index_seq n).
      * We need to show that (converges_to (fun k ↦ a(n(k)), L)).
      (** TODO: an equivalent to "apply with" would be nice here *)
      apply (squeeze_theorem (fun (k : ℕ) ↦ L - 1 / (INR k + 1))
        (fun (k : ℕ) ↦ (a (n k)))
        (sequence_ub a (i))).
      + (* apply squeeze_theorem with (c := sequence_ub a (i))
        (a := fun (k : ℕ) ↦ L - 1 / (INR k + 1)).*)
        To show : (∀ k  ∈ ℕ,
          L - 1 / (k + 1) <= a(n(k)) <= sequence_ub(a, i, k)).
        Take k ∈ ℕ.
        We show both statements.
        ** We need to show that (L - 1 / (k + 1) ≤ a (n k)).
          By (vi) it holds that (a (m k) > L - 1 / (k+1)).
          We conclude that (L - 1 / (k + 1) ≤ a (n k)).
        ** We need to show that (a (n k) ≤ sequence_ub a (i) k).
          By index_seq_grows_0 it holds that (m k ≥ k)%nat.
          By sequence_ub_bds we conclude that (a (n k) ≤ sequence_ub a (i) k).
      + (*TODO: fix not being able to use notation convergence with ''By ... we conclude that ...*)
        We need to show that (converges_to (fun k ↦ (L - 1 / (k + 1))) L).
        By lim_const_min_1_over_n_plus_1 we conclude that (converges_to (fun k ↦ L - 1 / (k + 1), L)).
      + By (sequence_ub_cv_to_L) we conclude that
        (converges_to (sequence_ub (a, i)) L).
Qed.

(** ## The Bolzano-Weierstrass Theorem*)
Theorem Bolzano_Weierstrass (a : ℕ → ℝ) :
  has_ub a ⇒ (has_lb a ⇒
    ∃ (n : ℕ → ℕ), ∃ (l : ℝ), is_index_seq n ∧
      converges_to (fun (k : ℕ) ↦ a (n k)) l ).
Proof.
    Assume that (has_ub a) (i).
    Assume that (has_lb a) (ii).
    Define iii := (maj_min a (i) (ii)).
    By Bolzano_Weierstrass_gen it holds that
      (∃ n0 : ℕ → ℕ, is_index_seq n0
        ∧ converges_to (fun (k : ℕ) ↦ a (n0 k)) (proj1_sig (_,_,lim_sup_bdd a (i) (iii)))) (iv).
    Obtain such an n0. It holds that
      (is_index_seq n0 ∧
        converges_to (fun (k : ℕ) ↦ a (n0 k)) (proj1_sig (_,_,lim_sup_bdd a (i) (iii)))) (v).
    Choose n := n0.
    Choose l := (proj1_sig (_,_,lim_sup_bdd a (i) (iii))).
    By (v) it suffices to show that (is_index_seq n ∧ converges_to (fun k ↦ a(n(k)), proj1_sig (_,_,lim_sup_bdd a (i) (iii)))).
    By (v) we conclude that (is_index_seq n ∧ converges_to (fun k ↦ a(n(k)), proj1_sig (_,_,lim_sup_bdd a (i) (iii)))).
Qed.

Lemma acc_pt_bds_seq_ub (a : ℕ → ℝ) (i : has_ub a) (x : ℝ) :
    is_seq_acc_pt a x ⇒ ∀ m : ℕ, x ≤ sequence_ub a (i) m.
Proof.
    Assume that (is_seq_acc_pt a x).
    It holds that (∃ n : ℕ → ℕ, is_index_seq n
      ∧ converges_to (fun k ↦ a(n(k)), x)).
    Obtain such an n. It holds that
      (is_index_seq n ∧ converges_to (fun k ↦ a(n(k)), x)) (iii).
    Because (iii) both (is_index_seq n) and (converges_to (fun k ↦ a(n(k)), x)) hold.
    Take m : ℕ.
    Define L := (sequence_ub a (i) m).
    We argue by contradiction.
    Assume that (~ x <= L).
    It holds that (L < x).
    Define ε := (x - L).
    It holds that (ε > 0).
    It holds that (∃ K ∈ ℕ, ∀ k : ℕ, (k ≥ K)%nat ⇒ R_dist (a (n k)) x < ε).
    Obtain such a K. Define N₀ := (Nat.max K m).
    It holds that (R_dist (a (n N₀)) x < ε).
    By Rabs_def2 it holds that (a (n N₀) - x < ε ∧ - ε < a (n N₀) - x) (v).
    Because (v) both (a (n N₀) - x < ε) and (- ε < a (n N₀) - x) hold.
    It holds that (x - a (n N₀) < x - L).
    It holds that (a (n N₀) > L).
    By index_seq_grows_0 it holds that (n N₀ ≥ N₀)%nat.
    It holds that (N₀ ≥ m)%nat.
    (* For speed, we have an explicit argument below *)
    (* By sequence_ub_bds it holds that (a (n N₀) ≤ L). *)
    We claim that (a (n N₀) ≤ L).
    {
      apply sequence_ub_bds.
      We conclude that ((n(N₀) ≥ m)%nat).
    }
    Contradiction.
Qed.

(** ## Comparing definitions of lim sup*)
Lemma lim_sup_bdd_is_lub_seq_acc_pts (a : ℕ → ℝ) (i : has_ub a) (ii : has_lb (sequence_ub a (i))) :
    is_lub (is_seq_acc_pt a) (proj1_sig (_,_, lim_sup_bdd a (i) (ii))).
Proof.
    (* TODO: fix that we refer to is_lub here. Moreover, we show both statements should work immediately. *)
    We need to show that
      (Raxioms.is_upper_bound (is_seq_acc_pt a) (proj1_sig (_,_, lim_sup_bdd a (i) (ii)))
      ∧ (for all b : ℝ, Raxioms.is_upper_bound (is_seq_acc_pt a) b ⇨ proj1_sig (_,_,lim_sup_bdd a (i) (ii)) ≤ b)).
    We show both statements.
    - We need to show that (Raxioms.is_upper_bound (is_seq_acc_pt a) (proj1_sig (_,_,lim_sup_bdd a (i) (ii)))).
      We need to show that (for all x : ℝ, is_seq_acc_pt a x ⇨ x ≤ proj1_sig (_,_,lim_sup_bdd a (i) (ii))).
      Take x : ℝ.
      Assume that (is_seq_acc_pt a x).
      By acc_pt_bds_seq_ub it holds that (∀ m : ℕ, x ≤ sequence_ub a (i) m).
      Define iii := (lim_sup_bdd a (i) (ii)).
      We need to show that (x ≤ proj1_sig (_,_,iii)).
      clear _defeq.
      Obtain such an l. simpl.
      By (low_bd_seq_is_low_bd_lim (sequence_ub a (i)))
          it holds that (l ≥ x).
      We conclude that (x ≤ l).
    - We need to show that (for all b : ℝ, Raxioms.is_upper_bound (is_seq_acc_pt a) b
        ⇨ proj1_sig (_,_,lim_sup_bdd a (i) (ii)) ≤ b).
      Take b : ℝ; such that (Raxioms.is_upper_bound (is_seq_acc_pt a) b).
      It holds that (for all x : ℝ, is_seq_acc_pt a x ⇨ x ≤ b).
      It holds that (for all x : ℝ,
        (∃ n : ℕ ⇨ ℕ, is_index_seq n ∧ converges_to (fun k ↦ a(n(k)), x)) ⇨ x ≤ b) (iii).
      By (iii) it suffices to show that (∃ n : ℕ ⇨ ℕ, is_index_seq n
        ∧ converges_to (fun k ↦ a(n(k))) (proj1_sig (_,_,lim_sup_bdd a (i) (ii)))).
      By Bolzano_Weierstrass_gen we conclude that (∃ n : ℕ ⇨ ℕ, is_index_seq n
        ∧ converges_to (fun k ↦ a(n(k))) (proj1_sig (_,_,lim_sup_bdd a (i) (ii)))).
Qed.

(** ## Some attempts to get nicer subsequences*)
(** In a sequence, either there are finitely many terms larger than or equal to a given number $L$, or for every $N$ there is an $n \geq N$ such that $a_n \geq L$.*)
Lemma finite_or_find_one (a : ℕ → ℝ) (L : ℝ) :
  (∃ N ∈ ℕ, ∀ k : ℕ, (k >= N)%nat ⇒ a k < L)
       ∨
    (∀ m ∈ ℕ, (∃ n ≥ m, (a n ≥ L)%R)%nat).
Proof.
    Define P := (∃ N ∈ ℕ, (∀ k ≥ N, (a k < L)%R)%nat).
    By classic it holds that (P \/ ~P) (i).
    Because (i) either P or (¬P) holds.
    - Case P.
      left.
      assumption.
    - Case (¬P).
      right.
      It holds that (~ ∃ N ∈ ℕ, (∀ k ≥ N, (a k < L)%R)%nat) (ii).
      We conclude that (∀ m ∈ ℕ, (∃ n ≥ m, (a(n) ≥ L)%R)%nat).
Qed.

Close Scope R_scope.
