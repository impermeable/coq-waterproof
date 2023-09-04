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

Require Import Coq.Reals.Reals.

Require Import Waterproof.Waterproof.
Require Import Waterproof.Automation.
Require Import Waterproof.Notations.
Require Import Waterproof.Tactics.

Local Open Scope R_scope.

(** * Test 1: show that we cannot conclude an implication. 
*)
Goal (0 = 0) -> (0 < 1).
  Fail We conclude that ((0 = 0) -> (0 < 1)).
Abort.

(** * Test 2: show that we cannot conclude a for all statement. 
*)
Goal forall x : R, (x^2 >= 0).
  Fail We conclude that (forall x : R, (x^2 >= 0)).
Abort.

Goal for all x : R, x + 3 = 3 + x.
  Fail We conclude that (for all x : R, x + 3 = 3 + x).
Abort.

(** * Test 3: show that we cannot conclude a there exists statement. 
*)
Goal exists y : R, y^2 > 0.
  Fail We conclude that (exists y : R, y^2 > 0).
Abort.

(** * Test 3: show that we cannot conclude a conjunction. 
*)
Goal forall x : R, (x - 0 = x) /\ (x + 3 = 3 + x).
  Take x : R.
  Fail We conclude that (x - 0 = x ∧ x + 3 = 3 + x).
Abort.

(** * Test 4: show that we cannot conclude a disjunction. 
*)
Goal forall x : R, (x^2 > 0) \/ (x + 3 = 3 + x).
  Take x : R.
  Fail We conclude that (x ^ 2 > 0 ∨ x + 3 = 3 + x).
Abort.

Waterproof Disable Automation Shield.

Waterproof Enable Automation RealsAndIntegers.

(** * Test 5: show that we can now conclude the implication. 
*)
Goal (0 = 0) -> (0 < 1).
  We conclude that ((0 = 0) -> (0 < 1)).
Qed.

(** * Test 6: show that we can now conclude the for all statement. 
*)
Goal forall x : R, (x^2 >= 0).
  We conclude that (forall x : R, (x^2 >= 0)).
Qed.

(* Test removed because this statement was too difficult for waterproof.
(** * Test 7: show that we can now conclude the there exists statement. 
*)
Goal exists y : R, y^2 > 0.
  Fail We conclude that (exists y : R, y^2 > 0).
Fail Qed.
Abort.
*)


(** * Test 8: show that we can now conclude the conjunction. 
*)
Goal forall x : R, (x - 0 = x) /\ (x + 3 = 3 + x).
  Take x : R.
  We conclude that (x - 0 = x ∧ x + 3 = 3 + x).
Abort.


(** * Test 9: show that we can now conclude the conjunction. 
*)
Goal forall x : R, (x^2 > 0) \/ (x + 3 = 3 + x).
  Take x : R.
  We conclude that (x ^ 2 > 0 ∨ x + 3 = 3 + x).
Abort.

Waterproof Enable Automation Shield.

(** * Test 13: show that we again cannot conclude the implication. 
*)
Goal forall x : R, (x^2 >= 0).
  Fail We conclude that ((0 = 0) -> (0 < 1)).
Abort.




(** * Test 14: too easy a statement that can be proven automatically, even without shielding.
*)
Goal forall x : R, x + 3 = x + 3.
  We conclude that (forall x : R, x + 3 = x + 3).
Abort.



(** Testing de Morgan laws. *)

Require Import Waterproof.Libs.Negation.
#[export] Hint Extern 1 => ltac2:(solve_by_manipulating_negation (fun () => ())) : wp_negation_logic.

(** Level 1 *)
Local Parameter P1 : R -> Prop.
(* Test 15 *)
Goal ~ (forall x : R, P1 x) -> (exists x : R, ~ (P1 x)).
Proof.
  intro H.
  We conclude that (there exists x : ℝ, ¬ P1 x).
Qed.

(* Test 16: similar as test 15 but with 'It suffices to show that ...' *)
Goal ~(for all x : R, P1 x).
Proof.
  It suffices to show that (there exists x : ℝ, ¬ P1 x).
Abort.

(** Level 2 *)
Local Parameter P2 : R -> R -> Prop.
(* Test 17 *)
Goal ~ (forall x : R, exists y : R, P2 x y) -> (exists x : R, ~ (exists y : R, P2 x y)).
Proof.
  intro H.
  We conclude that (there exists x : ℝ, ~ (exists y : R, P2 x y)).
Qed.

(* Test 17 *)
Goal (exists x : R, ~ (exists y : R, P2 x y)) -> (exists x : R, forall y : R, ~ P2 x y).
Proof.
  intro H.
  We conclude that (exists x : R, forall y : R, ~ P2 x y).
Qed.

(** Level 3 *)
(* Test 18 *)
Local Parameter P3 : R -> R -> R -> Prop.
Goal ~ (forall x : R, exists y : R, P2 x y) -> (exists x : R, ~ (exists y : R, P2 x y)).
Proof.
  intro H.
  We conclude that (there exists x : ℝ, ~ (exists y : R, P2 x y)).
Qed.

(* Test with assumptions on variables, like forall \eps > 0. *)
Definition Rdist (x y : R) := Rabs (x - y).
Local Parameter (f : R -> R) (a L : R).
(* Test 19 *)
Goal ~ (forall eps : R, eps > 0 -> exists delta : R, delta > 0 -> forall x : R, 
          0 < Rdist x a < delta -> Rdist (f x) L < eps)
      ->
     (exists eps : R, eps > 0 /\ ~(exists delta : R, delta > 0 -> forall x : R, 
          0 < Rdist x a < delta -> Rdist (f x) L < eps)).
Proof.
  intro H.
  We conclude that (there exists eps : ℝ , eps > 0
    ∧ ¬ (there exists delta : ℝ, delta > 0 ⇨ for all x : ℝ,
                       0 < Rdist x a < delta ⇨ Rdist (f x) L < eps)).
Qed.

(*Test 20: Similar as test 19, but with 'It suffices to show that ...'*)
Goal ~ (forall eps : R, eps > 0 -> exists delta : R, delta > 0 -> forall x : R, 
          0 < Rdist x a < delta -> Rdist (f x) L < eps).
Proof.
  It suffices to show that
     (exists eps : R, eps > 0 /\ ~(exists delta : R, delta > 0 -> forall x : R, 
          0 < Rdist x a < delta -> Rdist (f x) L < eps)).
Abort.