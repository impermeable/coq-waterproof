Require Import Notations.Common.
Require Import Notations.Sets.
Require Import Notations.Reals.

Require Import Coq.Reals.Reals.

Require Import Libs.Reals.Integer.

Open Scope R_scope.
Open Scope subset_scope.

Definition is_rational (q : ℝ) : Prop := ∃n ∈ Z_in_R, ∃m ∈ Z_in_R, 0 ≠ m ∧ q = n/m.

Definition Q_in_R : subset ℝ := fun y => exists x, Q2R(x) = y.

Lemma rational_tactic (q : ℝ) (n m : R) (h : 0 ≠ m ∧ q = n/m) (hn : n ∈ Z_in_R) (hm : m ∈ Z_in_R) 
    : is_rational q.
Proof.
    exists n.
    split.
    exact hn.
    exists m.
    split.
    exact hm.
    exact h.
Qed.

Lemma plus_frac (a b c d : ℝ) (hb : 0 ≠ b) (hd : 0 ≠ d) 
    : a/b + c/d = (a*d + c*b)/(b*d).
Proof.
    assert (b ≠ 0) as hb2.
    {
        intro hb2.
        rewrite hb2 in hb.
        apply hb.
        reflexivity.
    }
    assert (d ≠ 0) as hd2.
    {
        intro hd2.
        rewrite hd2 in hd.
        apply hd.
        reflexivity.
    }
    field.
    split; assumption.
Qed.

Lemma min_frac (a b c d : ℝ) (hb : 0 ≠ b) (hd : 0 ≠ d) 
    : a/b - c/d = (a*d - c*b)/(b*d).
Proof.
    assert (b ≠ 0) as hb2.
    {
        intro hb2.
        rewrite hb2 in hb.
        apply hb.
        reflexivity.
    }
    assert (d ≠ 0) as hd2.
    {
        intro hd2.
        rewrite hd2 in hd.
        apply hd.
        reflexivity.
    }
    field.
    split; assumption.
Qed.
