Require Import Stdlib.Reals.Reals.

Require Import Notations.Common.
Require Import Notations.Sets.

Open Scope R_scope.
Open Scope subset_scope.

Lemma archimedN (r : R) : exists n : nat, INR(n) > r.
Proof.
    assert (exists z : Z, IZR z > r) as h1.
    exists (up r).
    destruct (archimed r) as [h1 _].
    exact h1.
    destruct h1 as [z hz].
    destruct (Rtotal_order (IZR z) 0) as [h2 | h3].
    {
        exists 0%nat.
        apply (Rlt_trans _ (IZR z)).
        apply Rgt_lt.
        exact hz.
        simpl.
        exact h2.
    }
    destruct h3 as [h4 | h5].
    {
        exists (Z.to_nat z).
        rewrite INR_IZR_INZ.
        rewrite Znat.Z2Nat.id.
        exact hz.
        apply le_IZR.
        apply Req_le_sym.
        exact h4.
    }
    {
        exists (Z.to_nat z).
        rewrite INR_IZR_INZ.
        rewrite Znat.Z2Nat.id.
        exact hz.
        apply le_IZR.
        apply Rlt_le.
        exact h5.
    }
Qed.

Lemma archimedN_exists (r : R) : ∃ n ∈ nat, INR n > r.
Proof.
    destruct (archimedN r) as [m hm].
    exists m.
    split.
    unfold subset_in; unfold conv; trivial.
    exact hm.
Qed.

Notation "'the' 'Archimedean' 'property'" := archimedN_exists (at level 10).
