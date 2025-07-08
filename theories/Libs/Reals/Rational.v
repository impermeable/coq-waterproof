Require Import Notations.Common.
Require Import Notations.Sets.
Require Import Notations.Reals.

Require Import Coq.Reals.Reals.

Require Import Libs.Reals.Integer.

Open Scope R_scope.
Open Scope subset_scope.

Definition is_rational (q : ℝ) : Prop := ∃n ∈ Z_in_R, ∃m ∈ Z_in_R, 0 ≠ m ∧ q = n/m.

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

Lemma plus_frac (a b c d : ℝ) (hb : b ≠ 0) (hd : d ≠ 0) 
    : a/b + c/d = (a*d + b*c)/(b*d).
Proof.
    field.
    split; assumption.
Qed.

Lemma min_frac (a b c d : ℝ) (hb : b ≠ 0) (hd : d ≠ 0) 
    : a/b - c/d = (a*d - b*c)/(b*d).
Proof.
    field.
    split; assumption.
Qed.
