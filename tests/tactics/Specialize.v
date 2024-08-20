(******************************************************************************)
(*                  This file is part of Waterproof-lib.                      *)
(*                                                                            *)
(*   Waterproof-lib is free software: you can redistribute it and/or modify   *)
(*    it under the terms of the GNU General Public License as published by    *)
(*     the Free Software Foundation, either version 3 of the License, or      *)
(*                    (at your option) any later version.                     *)
(*                                                                            *)
(*     Waterproof-lib is distributed in the hope that it will be useful,      *)
(*      but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*       MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the         *)
(*               GNU General Public License for more details.                 *)
(*                                                                            *)
(*     You should have received a copy of the GNU General Public License      *)
(*   along with Waterproof-lib. If not, see <https://www.gnu.org/licenses/>.  *)
(*                                                                            *)
(******************************************************************************)

Require Import Ltac2.Ltac2.
Require Import Ltac2.Message.

Require Import Waterproof.Tactics.
Require Import Waterproof.Automation.

(** Test 0: This should be the expected behavior. *)
Goal (forall n : nat, n = n) -> True.
Proof.
intro H.
Use n := 3 in (H).
It holds that (3 = 3).
Abort.

(** Test 1: This should fail as the wrong variable name is chosen. *)
Goal (forall n : nat, n = n) -> True.
Proof.
intro H.
Fail Use m := (3) in (H).
Abort.

(** Test 2: This should fail because the wrong goal is specified. *)
Goal (forall n : nat, n = n) -> True.
Proof.
intro H.
Use n := (3) in (H).
Fail It holds that (True).
Abort.

(** Test 3: This should fail because first the wrapper needs to be resolved. *)
Goal (forall n : nat, n = n) -> True.
Proof.
intro H.
Use n := (3) in (H).
Fail exact I.
Abort.

(** It should be possible to use an outside lemma *)
Local Parameter F : nat -> nat.
Local Parameter F_identity : forall n : nat, F n = n.

Goal True.
Proof.
Fail It holds that (F 3 = 3).
Use n := (5) in (F_identity).
It holds that (F 5 = 5).
Abort.

(** Test 4: cannot use specialize tactic for function, 
  throw readable error message stating as much.  *)
Definition f : nat -> nat := fun (n : nat) => n.
Goal False.
Proof.
  Fail Use n := 5 in (f).
Abort.

(** Test 5: original universal quantifier hypohtesis left unchanged. *)
Goal (forall n : nat, n = n) -> True.
Proof.
intro H.
Use n := 3 in (H).
ltac1:(rename H into HH).   (* test for hypohtesis without producing output *)
Abort.

(** Test 6: multiple variable specifications  *)
Goal (forall n m : nat, n = m) -> False.
Proof.
intro H.
Use n := 3, m := 4 in (H).
It holds that (3 = 4).
Abort.

(** Test 7: multiple variable specifications, different order  *)
Goal (forall n m : nat, n = m) -> False.
Proof.
intro H.
Use m := 4, n := 3 in (H).
Fail It holds that (4 = 3). (* as expected :) *)
It holds that (3 = 4).
Abort.
