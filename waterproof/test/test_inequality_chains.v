(** * Testcases for [inequality_chains.v]
Authors: 
    - Jim Portegies
Creation date: 30 Oct 2021

Testcases for (in)equality chains.
--------------------------------------------------------------------------------

This file is part of Waterproof-lib.

Waterproof-lib is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

Waterproof-lib is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with Waterproof-lib.  If not, see <https://www.gnu.org/licenses/>.
*)

(* Tests for (in)equality chains *)

From Ltac2 Require Import Ltac2.
Require Import Waterproof.auxiliary.
Require Import Waterproof.test_auxiliary.

Load inequality_chains.

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
Fail pose (Aux.type_of (& 1 < 2 = 3 > 4)).
epose (Aux.type_of (& 1 < 2 = 3 > 4)). (* Does type check, evars are added ... *)
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
