Require Import Reals.
Require Import Waterproof.AllTactics.
Require Import Waterproof.notations.notations.
Require Import Reals.ROrderedType.
Require Import Waterproof.theory.analysis.reals. (* Req_true is in here *)
Require Import Waterproof.populate_database.waterproof_reals.
Require Import Waterproof.populate_database.all_databases.
Require Import Waterproof.load_database.RealNumbers.
Require Import micromega.Lra.

Open Scope R_scope.

Section Definitions.
Context (X : Metric_Space).


(* Definition metric_to_base := Base. *)

Coercion Base : Metric_Space >-> Sortclass.

Definition dist_positive :
  ∀ x y : X, dist X x y ≥ 0
  := dist_pos X.

Definition dist_non_degenerate :
  ∀ x y : X, (dist X x y = 0) ⇒ (x = y). 
  Take x, y : X.
  By (proj1(_,_,(dist_refl X x y))) we conclude that (dist X x y = 0 ⇨ x = y).
Defined.

Definition dist_symmetric :
  ∀ x y : X, dist X x y = dist X y x
  := dist_sym X.

Definition dist_triangle_inequality :
  ∀ x y z : X, dist X x z ≤ dist X x y + dist X y z.
  Take x, y, z : X. 
  By (dist_tri X) we conclude that (dist X x z ≤ dist X x y + dist X y z).
Qed.

Definition dist_reflexive : ∀ x : X, dist X x x = 0.
  Take x : X.
  By (proj2(_,_,(dist_refl X x x))) we conclude that (dist X x x = 0).
Defined.

End Definitions.



(** ** Expample : a discrete metric on the real line *)

Definition d_discrete_R : 
  ℝ → ℝ → ℝ := fun (x y : ℝ) => if Reqb x y then 0 else 3.

Lemma d'_eq_0 : forall x y : ℝ,
  d_discrete_R x y = 0 -> (Reqb x y) = true.
Proof.
Take x, y : ℝ.
Assume that (d_discrete_R x y = 0) (i).
Either (x = y) or (x ≠ y).
+ Case (x = y).
  By Req_true we conclude that (Reqb x y = true).

+ Case (x ≠ y).
  Expand the definition of d_discrete_R in (i).
  That is, write (i) as ( (if Reqb x y then 0 else 3) = 0).
  rewrite (Req_false x y n) in i.
  It holds that (3 ≠ 0).
  Contradiction.
Qed.

Lemma d'_eq_3 : forall x y : ℝ, d_discrete_R x y = 3 -> (Reqb x y) = false.
Proof.
Take x, y : ℝ. 
Assume that (d_discrete_R x y = 3) (i).
Expand the definition of d_discrete_R in (i).
That is, write (i) as ( (if Reqb x y then 0 else 3) = 3).
Either (x = y) or (x ≠ y).
+ Case (x = y).
  rewrite (Req_true x y e) in i.
  It holds that (0 ≠ 3).
  Contradiction.
+ Case (x ≠ y).
  By Req_false we conclude that (Reqb x y = false).
Qed.

Global Hint Resolve d'_eq_0 : reals.
Global Hint Resolve d'_eq_3 : reals.
Global Hint Extern 0 => unfold d_discrete_R; rewrite Req_true; lra : reals.
Global Hint Extern 0 => unfold d_discrete_R; rewrite Req_false; lra : reals.