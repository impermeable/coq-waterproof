From Ltac2 Require Import Ltac2.

Require Import Rbase.
Require Import Rfunctions.

Require Import Waterproof.AllTactics.
Require Import Waterproof.notations.notations.
Require Import Waterproof.load_database.RealsAndIntegers.


Local Open Scope R_scope.

(** * Test 7: show that we cannot conclude an implication. 
*)
Goal (0 = 0) -> (0 < 1).
  Fail We conclude that ((0 = 0) -> (0 < 1)).
Abort.

(** * Test 8: show that we cannot conclude a for all statement. 
*)
Goal forall x : R, (x^2 >= 0).
  Fail We conclude that (forall x : R, (x^2 >= 0)).
Abort.

Goal for all x : R, x + 3 = 3 + x.
  Fail We conclude that (for all x : R, x + 3 = 3 + x).
Abort.

(** * Test 9: show that we cannot conclude a there exists statement. 
*)
Goal exists y : R, y^2 > 0.
  Fail We conclude that (exists y : R, y^2 > 0).
Abort.



(* Disable not automatically proving quantifiers. *)
Ltac2 Set Waterproof.waterprove.waterprove.global_shield_automation := false.

(** * Test 10: show that we cannot conclude an implication. 
*)
Goal (0 = 0) -> (0 < 1).
  We conclude that ((0 = 0) -> (0 < 1)).
Qed.

(** * Test 11: show that we cannot conclude a for all statement. 
*)
Goal forall x : R, (x^2 >= 0).
  We conclude that (forall x : R, (x^2 >= 0)).
Qed.

(** * Test 12: show that we cannot conclude a there exists statement. 
*)
Goal exists y : R, y^2 > 0.
  Fail We conclude that (exists y : R, y^2 > 0).
Fail Qed. (*Some other issue..? TODO: investigate. *)
Abort.



(* Enable not automatically proving quantifiers. *)
Ltac2 Set Waterproof.waterprove.waterprove.global_shield_automation := true.

(** * Test 13: show that we cannot conclude an implication. 
*)
Goal (0 = 0) -> (0 < 1).
  Fail We conclude that ((0 = 0) -> (0 < 1)).
Abort.



(* De Morgan laws *)