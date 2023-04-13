Require Import Rbase.
Require Import Rfunctions.

Require Import Waterproof.AllTactics.
Require Import Waterproof.notations.notations.
Require Import Waterproof.theory.analysis.sup_and_inf_new_definitions.
Require Import Waterproof.load.
Module Import db := databases(RealsAndIntegers).

Open Scope R_scope.
Open Scope subset_scope.

Require Import Waterproof.set_debug_level.Info.
Require Import Waterproof.set_search_depth.To_5.

Set Default Goal Selector "!".
Set Default Timeout 5.

Goal forall a b: R, a <= b -> a + 1 < b + 2.
Proof.
  Take a, b: R.
  Assume that (a <= b).
  
  We conclude that (a + 1 < b + 2). 
Qed.

Local Parameter g : R -> R.
Local Parameter g_monotone : forall x y : R, x < y -> g x < g y.

Set Ltac2 Backtrace.

Goal forall a b : R, a < b -> 4 + g a < 5 + g b.
Proof.
  Take a, b : R.
  Assume that (a < b).

  By g_monotone we conclude that (4 + g a < 5 + g b).
Qed.

(* This works as it should *)
Goal forall e: R, e > 0 -> | -e | = e.
Proof.
  Take e: R.
  Assume that (e > 0).
  We conclude that (| -e | = e).
Qed.

(* This works as it should *)
Goal forall x r : R, r > 2 -> x = Rmax(0, 1) -> x < r.
Proof.
  Take x, r: R.
  Assume that (r > 2).
  Assume that (x = Rmax(0,1)).
  We conclude that (& x = Rmax(0,1) = 1 < 2 < r).
Qed.

(* OK *)
Goal forall t: R, | t * 1/t | >= 0.
Proof.
  Take t: R.
  We conclude that (|t * 1/t| >= 0).
Qed.

Goal forall r : R, r > 0 -> 0 <= 1 -> 0 <= 1 - Rmax( 0, 1 - r/2 ).
Proof.
  Take r: R.
  Assume that (r > 0).

  (* This works well *)
  It suffices to show that (0 <= 1 - Rmax(0, 1 - r/2)).

  It suffices to show that (Rmax(0, 1 - r/2) <= 1).
  
  It suffices to show that (0 <= 1 /\ 1 - r/2 <= 1).

  We show both statements.
  + We conclude that (0 <= 1).
  + We conclude that (1 - r / 2 <= 1).
Qed.

Goal (forall a b : R, a < 5 -> b < 5 -> (a < 3) \/ (b < 3) -> a + b < 8).
Proof.
  Take a, b: R.
  Assume that (a < 5).
  Assume that (b < 5).
  Assume that (a < 3 \/ b < 3).
  
  (* This should work *)
  (* Either (a < 3) or (b < 3). *)

  destruct __wp__h1.
  + We conclude that (a + b < 8).
  + We conclude that (a + b < 8).
Qed.

(*
  Maybe this works too well ?
  I think it would be better to write :
  `Either (a < b), (b < a) or (a = b).`
*)
Goal forall a b c: R, (a <= b -> c = b) /\ (b <= a -> c = a) -> b <= c.
Proof.
  Take a, b, c: R.
  Assume that ((a <= b -> c = b) /\ (b <= a -> c = a)).
  We conclude that (b <= c).
Qed.

Lemma expand_abs: forall x y: R, | x | < y -> -y < x < y.
Proof.
  Take x, y:R.
  Assume that (|x| < y).

  (* This should work *)
  (* We conclude that (-y < x < y). *)

  unfold Rabs in __wp__h.
  destruct (Rcase_abs).
  + It holds that (-y < x).
    It holds that (0 < y).

    (* This should work ? *)
    (* We conclude that (& -y < x < 0 < y). *)

    It holds that (x < y).
    We conclude that (-y < x < y).
  
  + (* This should work *)
    (* We conclude that (& -y < 0 < x < y). *)
    It holds that (-y < x).
    We conclude that (-y < x < y).
Qed.

Goal forall x r : R, r > 0 -> x = Rmax(0, 1 - r/2) -> | x - 1 | < r.
Proof.
  Take x, r: R.
  
  (* This works well *)
  Assume that (0 < r).

  Assume that (x = Rmax(0, 1 - r/2)).
  
  (* This should work *)
  (* We conclude that (& |Rmax(0,1) - 1| = |x - 1| < r). *)

  (* This should work *)
  (* It suffices to show that (|Rmax(0, 1 - r/2) - 1| < r). *)

  rewrite __wp__h0.
  By expand_abs it suffices to show that (-r < Rmax(0, 1 - r/2) - 1 < r).

  We show both statements.
  + admit.
  + (* This should work and give a better error message *)
    (* We conclude that (& Rmax(0, 1 - r/2) - 1 <= 1 - r/2 - 1 = -r/2 < 0 < r). *)
    admit.
Admitted.

Goal forall x: R, forall n: nat, (x > 0)%R -> pow x n >= 0.
Proof.
  Take x: R.
  Take n: nat.
  Assume that (x > 0).
  
  (* Why doesn't this work ? *)
  We use induction on n.
  + We first show the base case, namely (x ^ 0 >= 0).
    We conclude that (& x ^ 0 = 1 >= 0).
  + We now show the induction step.
    Assume that (x ^ n >= 0).
    
    (* This should work *)
    We conclude that (& x ^ (n+1) = x * x^n >= 0).
Qed.