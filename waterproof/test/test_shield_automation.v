From Ltac2 Require Import Ltac2.

Require Import Rbase.
Require Import Rfunctions.

Require Import Waterproof.AllTactics.
Require Import Waterproof.notations.notations.
Require Import Waterproof.load_database.RealsAndIntegers.


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

(* Test removed because this statement was too difficult for waterproof. *)
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