From mathcomp Require Import eqtype ssrbool ssralg ssrnum fintype.

Import Num.Def Num.Theory.

Require Import Waterproof.Waterproof.
Require Import Waterproof.Automation.
Require Import Waterproof.Tactics.
Require Import Waterproof.MathComp.

Waterproof Enable Automation Algebra.

Section eqtype_tests.

Variable T : eqType.
Variable x y : T.

Goal x = y \/ x != y.
Proof.
  We conclude that (x = y \/ x != y).
Qed.

Goal x != y \/ x = y.
Proof.
  We conclude that (x != y \/ x = y).
Qed.

Goal x == y \/ x != y.
Proof.
  We conclude that (x == y \/ x != y).
Qed.

Goal x = y \/ x <> y.
Proof.
  We conclude that (x = y \/ x <> y).
Qed.

Goal x <> y \/ x = y.
Proof.
  We conclude that (x <> y \/ x = y).
Qed.

End eqtype_tests.

Section derived_type_tests.

Variable n : nat.
Variable x y : 'I_n.

Goal x = y \/ x != y.
Proof.
  We conclude that (x = y \/ x != y).
Qed.

End derived_type_tests.

Section R_tests.
Open Scope ring_scope.

Variable R : numDomainType.
Variable x y : R.

Goal x \is Num.real -> y \is Num.real -> x <= y \/ x > y.
Proof.
  Assume that (x \is Num.real).
  Assume that (y \is Num.real).
  We conclude that (x <= y \/ x > y).
Qed.

Goal x \is Num.real -> x > 0 \/ x <= 0.
Proof.
  Assume that (x \is Num.real).
  We conclude that (x > 0 \/ x <= 0).
Qed.

Goal x \is Num.real -> y \is Num.real -> x < 0 \/ x >= 0.
Proof.
  Assume that (x \is Num.real).
  Assume that (y \is Num.real).
  We conclude that (x < 0 \/ x >= 0).
Qed.

Goal x \is Num.real -> y \is Num.real ->  x > y \/ x < y \/ x = y.
Proof.
  Assume that (x \is Num.real).
  Assume that (y \is Num.real).
  We conclude that (x > y \/ x < y \/ x = y).
Qed.

End R_tests.
