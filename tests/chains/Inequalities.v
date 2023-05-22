Require Import Ltac2.Ltac2.
Require Import Ltac2.Message.

Require Import Coq.Reals.Reals.

Require Import Waterproof.Waterproof.
Require Import Waterproof.Automation.
Require Import Waterproof.Chains.
Require Import Waterproof.Tactics.
Require Import Waterproof.Util.Assertions.
Require Import Waterproof.Util.Init.

(* Test 0: check if notations work. *)

Goal (& 3 < 4 <= 5 ≤ 7).
Abort.

Goal forall A : Type, forall a : A, & a = a = a = a.
Abort.

(* Test 1: sample proof *)
Goal (3 < 5) /\ (5 = 2 + 3) <-> (& 3 < 5 = 2 + 3).
split.
- intro H.
  cbn.
  destruct H.
  repeat split.
  + assumption.

- intro H.
  cbn in H.
  destruct H as [H1 H2].
  split.
  + assumption.
  + assumption.
Qed.

(* Test 2: check if terms of a subset can be coerced to terms of the underlying set (here: [R]). *)
Goal forall x : R, (& x < INR 0 = INR 0).
Abort.
(* Test 3 : different coercion, namely IZR *)
Goal forall x : R, (& x < up x = up x).
Abort.

(** More tests *)
(* Valid (though incorrect) inputs *)
Goal (& 1 = 2 = 2). Abort.
Goal (& 1 = 2 = 3 = 4). Abort.
Goal (& 1 = 2 < 3 = 4). Abort.
Goal (& 1 = 2 < 3 ≤ 4). Abort.
Goal (& 1 = 2 > 3 = 4). Abort.
Goal (& 1 ≥ 2 > 3 = 4). Abort.
(* Invalid input: combining < and > in one chain *)
Goal True.
Fail pose (type_of (& 1 < 2 = 3 > 4)).
epose (type_of (& 1 < 2 = 3 > 4)). (* Does type check, evars are added ... *)
Abort.
Fail Goal (& 1 < 2 = 3 > 4). (* Esoteric error. *)
(* Check for correctness global, weak global and total stamements. *)
Goal True.
assert_constr_equal (eval cbn in (& 1 = 2 = 3 = 4)) constr:((1 = 2 /\ 2 = 3) /\ 3 = 4).
(* Eval cbn in (global_statement (& 1 = 2 = 3 = 4)).*) (* Expected: 1 = 4 , :( *) (* Untestable *)
assert_constr_equal (eval cbn in (& 1 < 2 = 3 < 4)) constr:((1 < 2 /\ 2 = 3) /\ 3 < 4).
(*Eval cbn in (global_statement (1 &< 2 &< 3 &= 4)). (* Expected: 1 < 4 *) (* Untestable *)*)
(*Eval cbn in (weak_global_statement (1 &< 2 &< 3 &= 4)). (* Expected: 1 <= 4*) (* Untestable *)*)
assert_constr_equal (eval cbn in (& 1 > 2 > 3 = 4)) constr:((1 > 2 /\ 2 > 3) /\ 3 = 4). (* Expected: (1 > 2 /\ 2 > 3) /\ 3 = 4 *)
(*Eval cbn in (global_statement (1 &> 2 &> 3 &= 4)). (* Expected: 1 > 4 *) (* Untestable *)*)
(*Eval cbn in (weak_global_statement (1 &> 2 &> 3 &= 4)). (* Expected: 1 >= 4 *) (* Untestable *)*)
Abort.

(* Usage in hypotheses *)
Goal (& 1 < 2 < 3) -> (& 4 = 100 = 100) -> (1 < 3).
Proof.
  intros H1 H2.
  cbn in H1, H2.
Abort.
(* Usage in goal *)
Goal (& 1 < 2 <= 3 < 4).
Proof.
  repeat split; cbn.
Abort.

(** Test whether one can provide a custom relation for an EqualInterpretation.
*)
Local Parameter X : Type.
Require Import Relations.
Local Parameter rel : relation X.

#[local] Instance equal_setoid_interpretation : EqualInterpretation X :=
  { eq_rel_to_pred my_rel x y := rel x y
  }.

Local Parameter y : X.

Goal (& y = y = y).
change (rel y y /\ rel y y).
Abort.

Goal forall x : X, (& x = x = x).
intro x.
(* Test that the correct interpretation has been chosen *)
change (rel x x /\ rel x x).
Abort.

(** Test whether coercions from the naturals work for equalities over the reals numbers.
*)
Local Parameter rel_R : relation R.

#[local] Instance equal_setoid_interpretation_R : EqualInterpretation R :=
  { eq_rel_to_pred my_rel x y := rel_R x y
  }.

Goal forall x : R, (& 0%nat = x = 3%nat).
intro x.
(* Test that the correct interpretation has been chosen *)
change (rel_R 0%R x /\ rel_R x (1 + 1 + 1)%R).
Abort.
