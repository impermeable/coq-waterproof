Require Import Notations.Common.
Require Import Notations.Sets.

Open Scope subset_scope.

Lemma alternative_char_unique_exists {T : Type} (U : subset T) (P : T -> Prop):
    (∃! x ∈ U, P x) ↔ (∃ x ∈ U, P x ∧ ∀ y ∈ U, P y ⇒ y = x).
Proof.
    unfold unique_exists.
    split.
    {
        intros [[x [h1 h2]] h3].
        exists x.
        split.
        {
            exact h1.
        }
        {
            split.
            {
                exact h2.
            }
            {
                intros y h4 h5.
                apply h3.
                exact h4.
                exact h1.
                split.
                exact h5.
                exact h2.
            }
        }
    }
    {
        intros [x [h1 [h2 h3]]].
        unfold subset_type in x.
        split.
        {
            exists x.
            split.
            exact h1.
            exact h2.
        }
        {
            intros y h4 y' h5 [h6 h7].
            apply (@eq_trans _ _ x).
            {
                apply h3.
                exact h4.
                exact h6.
            }
            {
                symmetry.
                apply h3.
                exact h5.
                exact h7.
            }
        }
    }
Qed.
