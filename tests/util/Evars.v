Require Import Ltac2.Ltac2.
Require Import Waterproof.Waterproof.
Require Import Waterproof.Util.Evars.

Ltac2 Notation "rename_blank_evars_in_term_test" x(open_constr) :=
  rename_blank_evars_in_term "hi" x.

Goal (forall a b : nat, a + b = 0) -> True.
Proof.
rename_blank_evars_in_term_test (_ + _).
Abort.
