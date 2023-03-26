(** * Testcases for [we_conclude_that.v]
Authors: 
    - Lulof Pirée (1363638)
Creation date: 3 June 2021

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
From Ltac2 Require Import Int.


Require Import Waterproof.message.
Require Import Reals.
Require Import micromega.Lra.

Require Import Waterproof.test_auxiliary.
Require Import Waterproof.selected_databases.
Require Import Waterproof.set_intuition.Disabled.
Require Import Waterproof.set_search_depth.To_5.
Require Import Waterproof.populate_database.waterproof_reals.
Require Import Waterproof.populate_database.other_databases.
Require Import Waterproof.load_database.RealsAndIntegers.
Load we_conclude_that.
Require Import Waterproof.load_database.DisableWildcard.

Ltac2 store_verbosity := verbosity.

Ltac2 Set verbosity := fun () => if (le (test_verbosity ()) 0) 
    then -1 else (store_verbosity ()).

(* lra only works in the [R_scope] *)
Open Scope R_scope.
Lemma zero_lt_one: 0 < 1.
Proof.
    ltac1:(lra).
Qed.

(* -------------------------------------------------------------------------- *)
(** * Testcases for [We conclude that ... ] *)

(** * Test 1
    Base case: should easily be possible to finish the goal.
*)
Lemma test_we_conclude_1: True.
Proof.
    We conclude that True.
Qed.

(** * Test 2
    Error case: wrong goal provided.
*)
Lemma test_we_conclude_2: True.
Proof.
    let result () := We conclude that False in
    assert_raises_error result.
Abort.

(** * Test 3
    Warning case: provided goal is equivalent, 
        but uses an alternative notation.
*)
Lemma test_we_conclude_3: 2 = 2.
Proof.
    print (of_string "Should raise warning:").
    We conclude that (1+1 = 2).
Qed.

(** * Test 4
    Base case, like test 1 but more complex goal.
*)
Lemma test_we_conclude_4: forall A: Prop, (A \/ ~A  -> True).
Proof.
    intros A h.
    We conclude that (True).
Qed.

(** * Test 5
    Removed test case because it takes too long.

    Error case: Waterprove cannot find proof
    (because the statement is false!).

Lemma test_we_conclude_5: 0 = 1.
Proof.
    let result () := We conclude that (0 = 1) in
    assert_raises_error result.
Abort. *)

(** * Test 6
    Alternative [It follows that ...] notation.
*)
Lemma test_we_conclude_6: True.
Proof.
    It follows that True.
Qed.





(* -------------------------------------------------------------------------- *)
(** * Testcases for [By ... we conclude that ... ] *)

(** * Test 1
    Base case: should easily be possible to finish the goal,
    even with the provided lemma.

    NOTE: this test would also pass if we just
    write 
    [We conclude that (2 = 1).]
    Applarently, waterprove is powerful enough to apply symmetry to hypotheses.
*)
Lemma test_by_we_conclude_1: (1 = 2) -> (2 = 1).
Proof.
    intros h.
    apply eq_sym in h. (* Rewrite h as (2 = 1) using symmetry of "="*)
    By h we conclude that (2 = 1).
Qed.


(** * Test 2
    Remove test case as this required axiom.

    Base case: should easily be possible to finish the goal,
    but only with the given lemma.
Lemma test_by_we_conclude_2: 0 + 0 = 20.
Proof.
    
    assert (zero_plus_zero_is_twenty: 0+0 = 20).
    rewrite zero_is_ten. (* Get goal: [10 + 10 = 20]*)
    ltac1:(lra).

    (* This is just to test if the extra lemma is really needed: *)
    let failure () := We conclude that (0 + 0 = 10) in
    assert_raises_error failure.
    
    By zero_plus_zero_is_twenty we conclude that (0 + 0 = 20).
Qed.*)

(** * Test 3
    Warning case: provided goal is equivalent, 
        but uses an alternative notation.
*)
Lemma test_by_we_conclude_3: 2 = 1 + 1.
Proof.
    print (of_string "Should raise warning:").
    By zero_lt_one we conclude that (2 = 2).
Qed.

(** * Test 4
    Removed test case as it takes too long.

    Error case: Waterprove cannot find proof
    (because the statement is false,
    even with the given lemma).
Lemma test_by_we_conclude_4: 0 = 1.
Proof.
    let result () := By zero_is_ten we conclude that (0 = 1) in
    assert_raises_error result.
Abort.*)

(** * Test 5
    Shows that [waterprove]
    can solve [(1 < 2)]
    without explcitly being given 
    the lemma that states [0 < 1].
*)
Lemma test_by_we_conclude_5: 1 < 2.
Proof.
    assert (useless: 1 = 1).
    reflexivity.
    By useless we conclude that (1 < 2).
Qed.

(** * Example for the SUM.
    Somewhat more realistic context.
*)

Open Scope nat_scope.
Inductive even : nat -> Prop :=
    even0 : even 0
  | evenS : forall x:nat, even x -> even (S (S x)).

Lemma sum_example_by_we_conclude: forall x:nat, x = 2 -> even x.
Proof.
    intros x h.
    rewrite h. (* Change the goal to "even 2"*)
    apply evenS. (* Change the goal to "even 0"*)
    By even0 we conclude that (even 0).
Qed.

Require Import Waterproof.definitions.inequality_chains.
Open Scope R_scope.

(** * Test 4
We make an exception on the goal check when the argument is a chain of inequalities
*)
Goal (3 < 5).
We conclude that (& 3 < 4 < 5).
Qed.

Goal (3 = 3).
We conclude that (& 3 = 3 = 3).
Qed.


Goal forall eps : R, eps > 0 -> (Rmin (eps / 2) 1 <= eps).
intro eps.
intro eps_gt_0.
assert (& Rmin (eps/2) 1 <= eps/2 <= eps).
auto with reals.
auto with reals.
Qed.

Close Scope R_scope.

(** 'We conclude that' should accept (in nat_scope) (& 3 &<4 &< 5) for (3<5).*)
Goal (3 < 5).
We conclude that (& 3 < 4 < 5).
Qed.

(** 'We conclude that' should accept (in nat_scope) (& 3 &<4 &<= 5) for (3<5).*)
Goal (3 < 5).
We conclude that (& 3 < 4 <= 5).
Qed.

(** 'We conclude that' should accept (in nat_scope) (& 3 &<4 &< 5) for (3<=5).*)
Goal (3 <= 5).
We conclude that (& 3 < 4 < 5).
Qed.


(** * Test 6
  Test whether wrapped goals requiring users to write out what they need to show
  can be solved immediately. It is irritating to have to write something like:
    'We need to show that (a < b).'
    'We conclude that (a < b).'
*)

Goal (StateGoal.Wrapper (0 = 0)).
Proof.
  We conclude that (0 = 0).
Qed.

(** * Test 7
  Test whether the tactic throws an error for other wrappers.
*)
Goal (Case.Wrapper (0 = 1) (0 = 0)).
Proof.
  Fail We conclude that (0 = 0).
Abort.

(** * Test 8 *)
(** Actually tests for [waterprove] automation suboutine, but this seemed like a 
    convenient place to test. *)
(** Tests whether the error points out which specific (in)equality in the chain does not hold. *)
Local Parameter A : Type.
Local Parameter x y z : A.

Goal (& x = y = z).
Proof.
Fail We conclude that (& x = y = z). (* Expected: unable to find proof (x = y) *)
Abort.

Goal (x = y) -> (& x = y = z).
Proof.
intro p.
Fail We conclude that (& x = y = z). (* Expected: unable to find proof (y = z) *)
Abort.

Ltac2 Set verbosity := store_verbosity.
