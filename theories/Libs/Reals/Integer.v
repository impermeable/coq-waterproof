Require Import Notations.Common.
Require Import Notations.Sets.

Require Import Coq.Reals.Reals.

Definition Z_in_R : subset R := fun r => exists z : Z, IZR z = r.

Open Scope R_scope.

Lemma plus_Z_in_R (n m : R) : n ∈ Z_in_R ⇒ m ∈ Z_in_R ⇒ (n + m) ∈ Z_in_R.
Proof.
    intros [n' hn'] [m' hm'].
    exists (n' + m')%Z.
    rewrite plus_IZR.
    rewrite hn'.
    rewrite hm'.
    reflexivity.
Qed.

Lemma minus_Z_in_R (n m : R) : n ∈ Z_in_R ⇒ m ∈ Z_in_R ⇒ (n - m) ∈ Z_in_R.
Proof.
    intros [n' hn'] [m' hm'].
    exists (n' - m')%Z.
    rewrite minus_IZR.
    rewrite hn'.
    rewrite hm'.
    reflexivity.
Qed.

Lemma mult_Z_in_R (n m : R) : n ∈ Z_in_R ⇒ m ∈ Z_in_R ⇒ (n * m) ∈ Z_in_R.
Proof.
    intros [n' hn'] [m' hm'].
    exists (n' * m')%Z.
    rewrite mult_IZR.
    rewrite hn'.
    rewrite hm'.
    reflexivity.
Qed.

Lemma neg_Z_in_R (n : R) : n ∈ Z_in_R ⇒ (-n) ∈ Z_in_R.
Proof.
    intros [n' hn'].
    exists (-n')%Z.
    rewrite opp_IZR.
    rewrite hn'.
    reflexivity.
Qed.

Lemma zero_Z_in_R : 0 ∈ Z_in_R.
Proof.
    exists 0%Z.
    reflexivity.
Qed.

Lemma one_Z_in_R : 1 ∈ Z_in_R.
Proof.
    exists 1%Z.
    reflexivity.
Qed.

Lemma two_Z_in_R : 2 ∈ Z_in_R.
Proof.
    exists 2%Z.
    reflexivity.
Qed.

Lemma INR_1 : INR(1%nat) = 1.
Proof.
    reflexivity.
Qed.

Lemma INR_0 : INR(0%nat) = 0.
Proof.
    reflexivity.
Qed.

Lemma ge_zero_gt_one (n : nat) : (INR n > 0) -> INR n >= 1.
Proof.
    rewrite <-INR_1.
    rewrite <-INR_0.
    intro h.
    apply Rle_ge.
    apply le_INR.
    apply INR_lt in h.
    exact h.
Qed.
