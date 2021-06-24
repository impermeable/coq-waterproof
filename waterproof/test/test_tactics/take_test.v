(** * take_test
Authors: 
    - Lulof Pirée (1363638)
    - Cosmin Manea (1298542)
Creation date: 17 May 2021

Testcases for the [Take] tactic.
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
From Ltac2 Require Option.
From Ltac2 Require Import Message.

Require Import Waterproof.test_auxiliary.
Load take.


(** Test 0: This should work fine *)
Goal forall n : nat, n <= 2*n.
    Take n : nat.
Abort.

(** Test 1: Also this should work fine *)
Goal forall n : nat, n <= 2*n.
    Take x : nat.
Abort.

(** Test 2: This should raise an error, because the type does not match*)
Goal forall n : nat, n <= 2*n.
    assert_raises_error (fun () => Take n : bool).
Abort.

(** Test 3: This should raise an error, 
    because [Take] solves forall-quatifiers *)
Goal exists n : nat, n <= 2*n.
    assert_raises_error (fun() => Take n : nat).
Abort.

(** Test 4: Multi argument testcase *)
Goal forall n : nat, forall m : nat, n + m <= 2*n + m.
    Take n : nat, m : nat.
Abort.

(** Test 5: Two sets of multiple variables of the same type. *)
Goal forall (n m k: nat)  (b1 b2: bool), Nat.odd (n + m + k) = andb b1 b2.
    Take n, m, k : nat, b1, b2: bool.
Abort.

(** Test 6: Two sets of multiple variables of the same type,
    but with different names *)
Goal forall (n m k: nat)  (b1 b2: bool), Nat.odd (n + m + k) = andb b1 b2.
    Take a, b, c : nat, d, e: bool.
Abort.

(** Test 7: not allowed to introduce so many bools *)
Goal forall (n m k: nat)  (b1 b2: bool), Nat.odd (n + m + k) = andb b1 b2.
    assert_raises_error (fun () => Take a, b, c, d, e: bool).
Abort.

(** Test 8: look how crazy many vars we can introduce*)
Goal forall (a b c d e f g: nat) (b1 b2: bool), 
    Nat.odd (a + b + c + d + e + f + g) = andb b1 b2.
    Take a, b, c, d, e, f, g : nat, b1, b2: bool.
Abort.

(** Test 9: This should give a helpful error.
    (Note that two variables have the same name "a"!)

    Currently it raises "Internal (err:(a is already used.))"
    which seems clear enough :)
    *)
Goal forall (a b c d e f g: nat) (b1 b2: bool), 
    Nat.odd (a + b + c + d + e + f + g) = andb b1 b2.
    assert_raises_error (fun() => Take a, b, c, d, e, f, g : nat, a, h: bool).
Abort.

(** Test 10: Two sets of multiple variables of the same type.
    But in a *different order* with different names.

    This should raise an error, as the order of introducing variables is different.
*)
Goal forall (n m k: nat)  (b1 b2: bool), Nat.odd (n + m + k) = andb b1 b2.
    assert_raises_error (fun() => Take y, u: bool, a, b, c : nat).
Abort.

Require Import Waterproof.definitions.set_definitions.
Notation is_in := Waterproof.definitions.set_definitions.is_in.

(** Test 11: Introduciing set variables
    For some reason, if [A] is a set,
    then the set of its elements isn't called [A]
    but [subsets_R_to_elements A].
    Anyway, that last thing works.
*)
Lemma test_with_sets : forall (A : subsets_R), forall (a : A), a = a -> True.
    Take A : subsets_R.
    Take a : (subsets_R_to_elements A).

    assert_hyp_has_type @A constr:(subsets_R).
    assert_hyp_has_type @a constr:(elements_R_satisfying (is_in A)).
    trivial.
Qed.

    