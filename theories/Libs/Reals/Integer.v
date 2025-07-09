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