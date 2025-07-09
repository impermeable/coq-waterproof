Require Import Notations.Common.
Require Import Notations.Sets.

Require Import Coq.Reals.Reals.

Open Scope R_scope.

Lemma mult_neq_zero (x y : R) (hnx : 0 <> x) (hny : 0 <> y) : 0 <> x * y.
Proof.
    intro hxy.
    apply eq_sym in hxy.
    destruct (Rmult_integral x y hxy) as [hx | hy].
    {
        apply hnx.
        symmetry.
        exact hx.
    }
    {
        apply hny.
        symmetry.
        exact hy.
    }
Qed.

Lemma Rdivid_ineq_interchange (a b c : R) (h : a = b/c) (hnc : 0 <> c) (hna : 0 <> a) : c = b/a.
Proof.
    destruct (Req_dec b 0) as [hb | hnb].
    {
        rewrite hb in h.
        unfold Rdiv in h.
        rewrite Rmult_0_l in h.
        exfalso.
        apply hna.
        symmetry.
        exact h.
    }
    {
        rewrite h.
        field.
        split.
        {
            apply not_eq_sym.
            exact hnc.
        }
        exact hnb.
    }
Qed.