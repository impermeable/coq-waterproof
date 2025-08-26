Require Import Notations.Common.
Require Import Notations.Sets.
Require Import Notations.Reals.
Require Import Waterproof.

Require Import Stdlib.Reals.Reals.

Require Import Libs.Reals.Integer.
Require Import Libs.Reals.RealInequalities.

Open Scope R_scope.
Open Scope subset_scope.

Definition is_rational (q : ℝ) : Prop := ∃ n ∈ Z_in_R, ∃ m ∈ Z_in_R, 0 ≠ m ∧ q = n/m.

Definition Q_in_R : subset ℝ := fun y => exists x, Q2R(x) = y.

Lemma rational_of {q : ℝ} {n m : R} (hq: q = n/m) (h : 0 ≠ m) (hn : n ∈ Z_in_R) (hm : m ∈ Z_in_R)
    : is_rational q.
Proof.
    exists n.
    split.
    exact hn.
    exists m.
    split.
    exact hm.
    split.
    exact h.
    exact hq.
Qed.

Lemma plus_frac (a b c d : ℝ) (hb : 0 ≠ b) (hd : 0 ≠ d)
    : a/b + c/d = (a*d + c*b)/(b*d).
Proof.
    field; split; apply not_eq_sym; assumption.
Qed.

Lemma min_frac (a b c d : ℝ) (hb : 0 ≠ b) (hd : 0 ≠ d)
    : a/b - c/d = (a*d - c*b)/(b*d).
Proof.
    field; split; apply not_eq_sym; assumption.
Qed.

Lemma int_is_rational (n : ℝ) (hn : n ∈ Z_in_R) : is_rational n.
Proof.
apply (@rational_of n n 1).
- field.
- apply not_eq_sym, R1_neq_R0.
- exact hn.
- apply one_Z_in_R.
Qed.


Lemma sum_is_rational (a b : ℝ) (ha : is_rational a) (hb : is_rational b)
    : is_rational (a + b).
Proof.
destruct ha as [n1 [hn1 [m1 [hm1 [hneq1 h1]]]]].
destruct hb as [n2 [hn2 [m2 [hm2 [hneq2 h2]]]]].
apply (@rational_of (a + b) (n1 * m2 + n2 * m1) (m1 * m2)).
- rewrite h1, h2; apply plus_frac; assumption.
- apply mult_neq_zero; assumption.
- apply plus_Z_in_R; apply mult_Z_in_R; assumption.
- apply mult_Z_in_R; assumption.
Qed.


Lemma diff_is_rational (a b : ℝ) (ha : is_rational a) (hb : is_rational b)
    : is_rational (a - b).
Proof.
destruct ha as [n1 [hn1 [m1 [hm1 [hneq1 h1]]]]].
destruct hb as [n2 [hn2 [m2 [hm2 [hneq2 h2]]]]].
apply (@rational_of (a - b) (n1 * m2 - n2 * m1) (m1 * m2)).
- rewrite h1, h2; apply min_frac; assumption.
- apply mult_neq_zero; assumption.
- apply minus_Z_in_R; apply mult_Z_in_R; assumption.
- apply mult_Z_in_R; assumption.
Qed.

Lemma mult_is_rational (a b : ℝ) (ha : is_rational a) (hb : is_rational b)
    : is_rational (a * b).
Proof.
destruct ha as [n1 [hn1 [m1 [hm1 [hneq1 h1]]]]].
destruct hb as [n2 [hn2 [m2 [hm2 [hneq2 h2]]]]].
apply (@rational_of (a * b) (n1 * n2) (m1 * m2)).
- rewrite h1, h2; field; split; intro H; [apply hneq2 | apply hneq1]; symmetry; exact H.
- apply mult_neq_zero; assumption.
- apply mult_Z_in_R; assumption.
- apply mult_Z_in_R; assumption.
Qed.

Lemma div_is_rational (a b : ℝ) (ha : is_rational a) (hb : is_rational b)
    : 0 ≠ b → is_rational (a / b).
Proof.
destruct ha as [n1 [hn1 [m1 [hm1 [hneq1 h1]]]]].
destruct hb as [n2 [hn2 [m2 [hm2 [hneq2 h2]]]]].
intros hneqb.
assert (0 ≠ n2) as hneq_n2.
{ intro H; apply hneqb; rewrite h2, <- H; unfold Rdiv; rewrite Rmult_0_l; reflexivity. }
apply (@rational_of (a / b) (n1 * m2) (m1 * n2)).
- (* Show a / b = (n1 * m2)/(m1 * n2) *)
  rewrite h1, h2.
  field.
  split.
  * exact (not_eq_sym hneq_n2).
  * split; apply not_eq_sym; assumption.
- (* Show 0 ≠ m1 * n2 *)
  apply mult_neq_zero; [exact hneq1 | exact hneq_n2].
- (* Show n1 * m2 ∈ Z_in_R *)
  apply mult_Z_in_R; assumption.
- (* Show m1 * n2 ∈ Z_in_R *)
  apply mult_Z_in_R; assumption.
Qed.

Lemma neg_is_rational (a : ℝ) (ha : is_rational a) : is_rational (-a).
Proof.
destruct ha as [n [hn [m [hm [hneq h]]]]].
apply (@rational_of (-a) (-n) m).
- rewrite h; field; apply not_eq_sym; exact hneq.
- exact hneq.
- (* Show -n ∈ Z_in_R *)
  assert (0 - n = -n) as H0.
  { ring. }
  rewrite <- H0.
  apply (minus_Z_in_R 0 n).
  + apply zero_Z_in_R.
  + exact hn.
- exact hm.
Qed.
