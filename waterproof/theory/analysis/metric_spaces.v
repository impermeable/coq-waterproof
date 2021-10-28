Require Import Reals.
Require Import Waterproof.AllTactics.
Require Import Waterproof.notations.notations.
Require Import Reals.ROrderedType.
Require Import Waterproof.databases. (* Req_true is in here *)

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
  Take x, y : X. Apply (dist_refl X). Defined.

Definition dist_symmetric :
  ∀ x y : X, dist X x y = dist X y x
  := dist_sym X.

Definition dist_triangle_inequality :
  ∀ x y z : X, dist X x z ≤ dist X x y + dist X y z.
  Take x, y, z : X. Apply (dist_tri X).
Qed.

Definition dist_reflexive : ∀ x : X, dist X x x = 0.
  Take x : X. Apply (dist_refl X). We need to show that (x = x).
  We conclude that (x = x).
Defined.

End Definitions.

(** ** Expample : the discrete metric on the real line *)

Definition d_discrete_R : 
  ℝ → ℝ → ℝ := fun (x y : ℝ) => if Reqb x y then 0 else 1.

Lemma d'_eq_0 : forall x y : ℝ,
  d_discrete_R x y = 0 -> (Reqb x y) = true.
Proof.
Take x, y : ℝ. 
Assume d'_0 : (d_discrete_R x y = 0).
Either (x = y) or (x ≠ y).
+ Case (x = y).
  Apply Req_true.
  Apply e.

+ Case (x ≠ y).
  Expand the definition of d_discrete_R in d'_0.
  That is, write d'_0 as ( (if Reqb x y then 0 else 1) = 0).
  rewrite (Req_false x y n) in d'_0.
  It holds that H1 : (1 ≠ 0).
  Contradiction.
Qed.

Lemma d'_eq_1 : forall x y : ℝ, d_discrete_R x y = 1 -> (Reqb x y) = false.
Proof.
Take x, y : ℝ. 
Assume d'_1 : (d_discrete_R x y = 1).
Expand the definition of d_discrete_R in d'_1.
That is, write d'_1 as ( (if Reqb x y then 0 else 1) = 1
).
Either (x = y) or (x ≠ y).
+ Case (x = y).
  rewrite (Req_true x y e) in d'_1.
  It holds that H1 : (0 ≠ 1).
  Contradiction.
+ Case (x ≠ y).
  Apply Req_false.
  Apply n.
Qed.

Global Hint Resolve d'_eq_0 : reals.
Global Hint Resolve d'_eq_1 : reals.
Global Hint Extern 0 => unfold d_discrete_R; rewrite Req_true; lra : reals.
Global Hint Extern 0 => unfold d_discrete_R; rewrite Req_false; lra : reals.