From mathcomp Require Import ssreflect ssrbool eqtype ssrnum.

Import Num.Def Num.Theory.

Lemma bool_prop_equiv (T : eqType) (x y : T) : (x = y) <-> (x == y).
  split.
  -move=>H.
  by apply/eqP.
  -move=>H.
  by apply/eqP.
Qed.

Lemma bool_prop_equiv2 (T : eqType) (x y : T) : (x <> y) <-> (x != y).
  split.
  -move=>H.
  by apply/eqP.
  -move=>H.
  by apply/eqP.
Qed.

Lemma neq_sym (T : eqType) (x y : T) : x != y -> y != x.
Proof.
  move => H.
  by rewrite eq_sym in H.
Qed.

(* We import Ltac2 here, so that we can use ssreflect and ltac1 above *)
From Ltac2 Require Import Ltac2 Message.

Ltac2 do_case (lemma: constr) :=
  ltac1:(lemma |- case: lemma; try intro; try assumption) (Ltac1.of_constr lemma).

Ltac2 proof_disjunction_using (lemma: constr) :=
  do_case (lemma);
  try (apply or_introl; apply is_true_true);
  try (apply or_introl; assumption);
  try (apply or_intror; apply is_true_true);
  try (apply or_intror; assumption).

Ltac2 proof_disjunction2 () :=

  try (ltac1:(rewrite [_ = _]bool_prop_equiv));
  try (ltac1:(rewrite [_ <> _]bool_prop_equiv2));

  first [
    proof_disjunction_using constr:(real_leP)   |
    proof_disjunction_using constr:(real_ltP)   |
    proof_disjunction_using constr:(real_ge0P)  |
    proof_disjunction_using constr:(real_le0P)  |
    (* Okay, so the order of trying these things does matter here. 
      trying to do eqVneq first does not work with proving goals of the type 
      normr (x - y) = x - y \/ normr (x - y) = y - x *)
    proof_disjunction_using constr:(@eqVneq)
  ].

Ltac2 proof_disjunction3 () :=
  try (ltac1:(rewrite [_ = _]bool_prop_equiv));
  try (ltac1:(rewrite [_ <> _]bool_prop_equiv2));
  do_case constr:(@real_ltgtP);
  auto.

#[export] Hint Extern 1 (_ \/ _) => ltac2:(proof_disjunction2 ()) : wp_decidability_classical.
#[export] Hint Extern 1 (_ \/ _) => ltac2:(proof_disjunction2 ()) : wp_core.
#[export] Hint Extern 1 (_ \/ _ \/ _) => ltac2:(proof_disjunction3 ()) : wp_decidability_classical.
#[export] Hint Extern 1 (_ \/ _ \/ _) => ltac2:(proof_disjunction3 ()) : wp_core.
#[export] Hint Resolve eq_sym : wp_core.
#[export] Hint Resolve neq_sym : wp_core.