(** * Testcases for [propagate_negation_backwards.v]
Authors: 
    - Jelle Wemmenhove

Creation date: 3 Nov 2021

TODO: description

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

Load propagate_negation_backwards.

Variable P : nat -> nat -> nat -> Prop.
Goal forall z : nat, ~ P 0 0 z.
Proof.
  propagate_negation_backwards ().
Abort.

Goal exists z : nat, ~ P 0 0 z.
Proof.
  propagate_negation_backwards ().
Abort.

Goal forall y : nat, forall z : nat, ~ P 0 y z.
Proof.
  propagate_negation_backwards ().
  propagate_negation_backwards ().
Abort.
  
Goal forall x : nat, exists y : nat, forall z : nat, ~ P x y z.
Proof.
  propagate_negation_backwards ().
  propagate_negation_backwards ().
  propagate_negation_backwards ().
Abort.

Goal forall z : nat, (~ P 0 0 z) \/ (~ P z 0 0).
Proof.
  propagate_negation_backwards ().
  propagate_negation_backwards ().
Abort.

Goal forall z : nat, (~ P 0 0 z) /\ (~ P z 0 0).
Proof.
  propagate_negation_backwards ().
  propagate_negation_backwards ().
Abort.

Goal forall z : nat, (P 0 0 z) /\ (~ P z 0 0).
Proof.
  propagate_negation_backwards ().
  propagate_negation_backwards ().
Abort.

Goal forall z : nat, (P 0 0 z) -> (~ P z 0 0).
Proof.
  propagate_negation_backwards ().
  propagate_negation_backwards ().
Abort.

Variable Q : Prop.
Goal Q \/ (forall z : nat, ~ P 0 0 z).
Proof.
  propagate_negation_backwards ().
Abort.

Goal Q /\ (forall z : nat, ~ P 0 0 z).
Proof.
  propagate_negation_backwards ().
  propagate_negation_backwards ().
Abort.

Goal Q -> (forall z : nat, ~ P 0 0 z).
Proof.
  propagate_negation_backwards ().
  propagate_negation_backwards ().
  Fail propagate_negation_backwards ().
Abort.

Goal forall x : nat, exists y : nat, P x y 0.
Proof.
  Fail propagate_negation_backwards ().
Abort.

Goal sig (fun z : nat => ~ P 0 0 z).
Proof.
  Fail propagate_negation_backwards ().
Abort.


(* Big test with example from analysis: not (f(x) --> L as x --> a). *)
Require Import Reals.
Open Scope R_scope.

Definition Rdist (x y : R) := Rabs (x - y).
Variable (f : R -> R) (a L : R).
Goal ~ (forall eps : R, eps > 0 -> exists delta : R, delta > 0 -> forall x : R, 
          0 < Rdist x a < delta -> Rdist (f x) L < eps)
      ->
     (exists eps : R, eps > 0 /\ (forall delta : R, delta > 0 /\ (exists x : R, 
          0 < Rdist x a < delta /\ ~ Rdist (f x) L < eps))).
Proof.
  intro H.
  propagate_negation_backwards ().
  propagate_negation_backwards ().
  propagate_negation_backwards ().
  propagate_negation_backwards ().
  propagate_negation_backwards ().
  propagate_negation_backwards ().
  exact H.
Qed.

Close Scope R_scope.
