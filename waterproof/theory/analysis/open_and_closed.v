Require Import Reals.
Require Import Classical_Prop.
Require Import Waterproof.AllTactics.
Require Import Waterproof.notations.notations.
Require Import Waterproof.load.
Import databases_RealsAndIntegers.
Require Import Waterproof.set_search_depth.To_5.

Open Scope R_scope.
Open Scope subset_scope.

(** Definitions *)
Definition open_ball (p : R) (r : R) : subset R := as_subset _ (fun x => | x - p | < r).

Definition is_interior_point (a : R) (A : R -> Prop) :=
  there exists r : R, (r > 0) /\ (for all x : R, x : (open_ball a r) -> A x).

Definition is_open (A : R -> Prop) := for all a : R, A a -> is_interior_point a A.

Definition complement (A : R -> Prop) : subset R := as_subset _ (fun x => not (A x)).

Definition is_closed (A : R -> Prop) := is_open (complement A).


(** Notations *)
Notation "B( p , r )" := (open_ball p r) (at level 68, format "B( p ,  r )").
Local Ltac2 unfold_open_ball    ()          := unfold open_ball, pred.
Local Ltac2 unfold_open_ball_in (h : ident) := unfold open_ball, pred in $h.
Ltac2 Notation "Expand" "the" "definition" "of" "B" cl(opt(seq("in", "(", ident, ")"))) := 
  expand_def_framework unfold_open_ball unfold_open_ball_in cl.
Ltac2 Notation "Expand" "the" "definition" "of" "open" "ball" cl(opt(seq("in", "(", ident, ")"))) := 
  expand_def_framework unfold_open_ball unfold_open_ball_in cl.

Notation "a 'is' 'an' '_interior' 'point_' 'of' A" := (is_interior_point a A) (at level 68).
Notation "a 'is' 'an' 'interior' 'point' 'of' A" := (is_interior_point a A) (at level 68, only parsing).
Local Ltac2 unfold_is_interior_point    ()          := unfold is_interior_point.
Local Ltac2 unfold_is_interior_point_in (h : ident) := unfold is_interior_point in $h.
Ltac2 Notation "Expand" "the" "definition" "of" "interior" "point" cl(opt(seq("in", "(", ident, ")"))) := 
  expand_def_framework unfold_is_interior_point unfold_is_interior_point_in cl.

Notation "A 'is' '_open_'" := (is_open A) (at level 68).
Notation "A 'is' 'open'" := (is_open A) (at level 68, only parsing).
Local Ltac2 unfold_is_open    ()          := unfold is_open.
Local Ltac2 unfold_is_open_in (h : ident) := unfold is_open in $h.
Ltac2 Notation "Expand" "the" "definition" "of" "open" cl(opt(seq("in", "(", ident, ")"))) := 
  expand_def_framework unfold_is_open unfold_is_open_in cl.


Notation "'ℝ\' A" := (complement A) (at level 20, format "'ℝ\' A").
Notation "'ℝ' '\' A" := (complement A) (at level 20, only parsing).
Local Ltac2 unfold_complement    ()          := unfold complement, pred.
Local Ltac2 unfold_complement_in (h : ident) := unfold complement, pred in $h.
Ltac2 Notation "Expand" "the" "definition" "of" "ℝ\" cl(opt(seq("in", "(", ident, ")"))) := 
  expand_def_framework unfold_complement unfold_complement_in cl.
Ltac2 Notation "Expand" "the" "definition" "of" "complement" cl(opt(seq("in", "(", ident, ")"))) := 
  expand_def_framework unfold_complement unfold_complement_in cl.

Notation "A 'is' '_closed_'" := (is_closed A) (at level 68).
Notation "A 'is' 'closed'" := (is_closed A) (at level 68, only parsing).
Local Ltac2 unfold_is_closed    ()          := unfold is_closed.
Local Ltac2 unfold_is_closed_in (h : ident) := unfold is_closed in $h.
Ltac2 Notation "Expand" "the" "definition" "of" "closed" cl(opt(seq("in", "(", ident, ")"))) :=
  expand_def_framework unfold_is_closed unfold_is_closed_in cl.


(** Hints *)
Lemma zero_in_interval_closed_zero_open_one : (0 : [0,1)).
Proof.
  We need to show that (0 <= 0 /\ 0 < 1).
  We show both (0 <= 0) and (0 < 1).
  - We conclude that (0 <= 0).
  - We conclude that (0 < 1).
Qed.
#[export] Hint Resolve zero_in_interval_closed_zero_open_one : wp_reals.

Lemma one_in_complement_interval_closed_zero_open_one : (1 : ℝ \ [0,1)).
Proof.
  We need to show that (~ ((0 <= 1) /\ (1 < 1))).
  It suffices to show that (~ 1 < 1).
  We conclude that (~ 1 < 1).
Qed.
#[export] Hint Resolve one_in_complement_interval_closed_zero_open_one : wp_reals.

#[export] Hint Resolve Rabs_def1 : wp_reals.
#[export] Hint Resolve not_and_or : wp_classical_logic.

Lemma not_in_compl_implies_in (A : subset R) (x : R) : (¬ x : ℝ\A) -> (x : A).
Proof. Assume that (¬ x : ℝ\A). It holds that (¬ ¬ x : A). We conclude that (x : A). Qed.
Lemma in_implies_not_in_compl (A : subset R) (x : R) : (x : A) -> (¬ x : ℝ\A).
Proof. Assume that (x : A). We conclude that (¬ x : ℝ\A). Qed.
#[export] Hint Resolve not_in_compl_implies_in : wp_negation_reals.
#[export] Hint Resolve in_implies_not_in_compl : wp_negation_reals.


Close Scope subset_scope.
Close Scope R_scope.
