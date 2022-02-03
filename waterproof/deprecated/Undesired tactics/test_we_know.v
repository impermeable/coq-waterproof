(** * Testcases for [we_know.v]
Authors: 
    - Lulof Pirée (1363638)
    - Cosmin Manea (refactored file)

Creation date: 17 June 2021

Testcases for the [We know ... : ...] tactic.
Tests pass if they can be run without unhandled errors.
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

From Ltac2 Require Import Ltac2.
Require Import Arith.

Load we_know.
Require Import Waterproof.auxiliary.
Require Import Waterproof.test_auxiliary.


(** Test 1: basic functionality of [We know H:...] *)
Goal forall x: nat, x = 3 -> x < 4.
    intros.
    We know H : (x = 3).
    assert (four_is_S_three: 4 = S x).
        rewrite H.
        reflexivity.
    assert (x_smaller_than_succ: x < S x).
        apply gt_Sn_n.
    rewrite <- four_is_S_three in x_smaller_than_succ.
    exact x_smaller_than_succ.
Qed.



(** Test 2: Basic functionality of the [By...we know...] variant  *)
Goal forall n m : nat, (n = m) <-> (n + 1 = m + 1).
Proof.
    intros.
    split.
    intros.
    By H we know (n = m).
    auto with *.
Abort.


(** Test 3: Basic functionality of the [By...we know...] variant in the content of a result 
    proven during a proof*)
Goal True.
Proof.
    assert (forall n : nat, n = n) as X.
    {
      intro.
      reflexivity.
    }
    By X we know (forall n : nat, n = n).
    auto.
Qed.



(** Test 4: [We know Z : T] should fail in case [Z] is undefined,
    or the type [T] does not match 
    the type of the variable [Z] in the context *)
Goal forall x: nat, x = 3 -> x < 4.
    intros.
    assert_raises_error (fun () => We know H: (x = 999)).
    assert_raises_error (fun () => We know Z: (x = 4)).
Abort.



Definition double := fun (x: nat) => 2*x.

(** Test 5: this test shows why we need [eval cbv in $t].
    Without [eval cbv in], [t] would contain [double x],
    while this gets replaced by its definition in 
    [eval cbv in (type_of $h)]. *)
Goal forall x: nat, double x = 4 -> x = 2.
    intros.
    We know H : (double x = 4).
Abort.