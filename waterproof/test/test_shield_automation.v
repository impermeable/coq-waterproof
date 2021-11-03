From Ltac2 Require Import Ltac2.

Require Import Rbase.
Require Import Rfunctions.

Require Import Waterproof.AllTactics.
Require Import Waterproof.notations.notations.
Require Import Waterproof.load_database.All.


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



(* Disable automation shielding. *)
Ltac2 Set Waterproof.waterprove.waterprove.global_shield_automation := false.

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




(* Enable automation shielding. *)
Ltac2 Set Waterproof.waterprove.waterprove.global_shield_automation := true.

(** * Test 13: show that we again cannot conclude the implication. 
*)
Goal (0 = 0) -> (0 < 1).
  Fail We conclude that ((0 = 0) -> (0 < 1)).
Abort.




(** * Test 14: too easy a statement that can be proven automatically, even without shielding.
*)
Goal forall x : R, x + 3 = x + 3.
  We conclude that (forall x : R, x + 3 = x + 3).
Abort.


(* Testing de Morgan laws. *)

(* Level 1 *)
Variable P1 : R -> Prop.
Goal ~ (forall x : R, P1 x) -> (exists x : R, ~ (P1 x)).
Proof.
  intro H.
  We conclude that (there exists x : ℝ, ¬ P1 x).
Qed.

(* Level 2 *)
Variable P2 : R -> R -> Prop.
Goal ~ (forall x : R, exists y : R, P2 x y) -> (exists x : R, ~ (exists y : R, P2 x y)).
Proof.
  intro H.
  We conclude that (there exists x : ℝ, ~ (exists y : R, P2 x y)).
Qed.

Goal (exists x : R, ~ (exists y : R, P2 x y)) -> (exists x : R, forall y : R, ~ P2 x y).
Proof.
  intro H.
  Fail We conclude that (exists x : R, forall y : R, ~ P2 x y).
Abort.



(* Level 3 *)
Variable P3 : R -> R -> R -> Prop.
Goal ~ (forall x : R, exists y : R, P2 x y) -> (exists x : R, ~ (forall y : R, P2 x y)).
Proof.
  intro H.
  Fail We conclude that (there exists x : ℝ, ~ (forall y : R, P2 x y)).
Abort.

(* Test with assumptions on variables, like forall \eps > 0. *)
Definition Rdist (x y : R) := Rabs (x - y).
Variable (f : R -> R) (a L : R).
Goal ~ (forall eps : R, eps > 0 -> exists delta : R, delta > 0 -> forall x : R, 
          0 < Rdist x a < delta -> Rdist (f x) L < eps)
      ->
     (exists eps : R, eps > 0 /\ ~(exists delta : R, delta > 0 -> forall x : R, 
          0 < Rdist x a < delta -> Rdist (f x) L < eps)).
Proof.
  intro H.
  Fail
  We conclude that (there exists eps : ℝ , eps > 0
    ∧ ¬ (there exists delta : ℝ, delta > 0 ⇨ for all x : ℝ,
                       0 < Rdist x a < delta ⇨ Rdist (f x) L < eps)).
Abort.
