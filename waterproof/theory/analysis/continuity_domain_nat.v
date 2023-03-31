Set Default Timeout 3.

Require Import Reals.
Require Import Waterproof.AllTactics.
Require Import Waterproof.notations.notations.
Require Import Waterproof.load.
Import databases_RealsAndIntegers.
Require Import Waterproof.set_search_depth.To_5.
(* Require Import Waterproof.load_database.Intuition. *)

Open Scope R_scope.

(** Definitions *)
Section metricspace.
Variable X : Metric_Space.
Coercion Base : Metric_Space >-> Sortclass.

Definition is_accumulation_point (a : R) :=
  for all ε : R, (ε > 0) ⇒
    there exists n : nat, 0 < | n - a | < ε.

Definition is_isolated_point (a : R) :=
  there exists ε : R, (ε > 0) ∧
    (for all n : nat, |n - a| = 0 ∨ (ε ≤ |n - a|)).

Definition limit_in_point (f : ℕ → X) (a : ℕ) (L : X) :=
 for all ε : R, (ε > 0) ⇒
   there exists δ : R, (δ > 0) ∧
     (for all n : nat,
       (0 < |n - a| < δ) ⇒ (dist X (f n) L < ε)).

Definition is_continuous_in (f : ℕ → X) (a : ℕ) :=
  ((is_accumulation_point a) ∧ (limit_in_point f a (f a))) ∨ (is_isolated_point a).

End metricspace.

(** Hints *)
Lemma aux1 : for all n m : ℕ, (n = m) ⇒ |m - n| = |n - n|.
Proof.
  Take n, m : ℕ. Assume that (n = m).
  We conclude that (& |m - n| = |m - m| = m - m = 0 = n - n = |n - n|).
Qed.
#[export] Hint Resolve aux1 : wp_reals.
(** Useful lemma *)
Lemma useful_lemma : for all n m : ℕ, (n ≠ m) ⇒ (1 ≤ | m - n |).
Proof.
  Take n, m : ℕ. Assume that (n ≠ m).
  assert (n > m ∨ n < m)%nat as i by (apply Nat.lt_gt_cases; auto).
  Because (i) either (n > m)%nat or (n < m)%nat holds.
  + Case (n > m)%nat.
    It holds that (n ≥ S m)%nat.
    By S_INR it holds that (m + 1 = S m).
    It holds that (m + 1 - m = S m - m).
    It holds that ((S m) ≤ n).
    It holds that ((S m) - m ≤ n - m).
    We conclude that
        (& 1 = m + 1 - m = (S m) - m ≤ n - m = | n - m | = | m - n | ).
  + Case (n < m)%nat.
    It holds that (S n ≤ m)%nat.
    By S_INR it holds that (n + 1 = S n).
    It holds that (n + 1 - n = S n - n).
    It holds that ((S n) ≤ m).
    It holds that ((S n) - n ≤ m - n).
    We conclude that (& 1 = n + 1 - n = (S n) - n ≤ m - n = |m - n|).
Qed.

(** Notations *)
Notation "a 'is' 'an' '_accumulation' 'point_'" := (is_accumulation_point a) (at level 68).
Notation "a 'is' 'an' 'accumulation' 'point'" := (is_accumulation_point a) (at level 68, only parsing).
Local Ltac2 unfold_is_accumulation_point    ()          := unfold is_accumulation_point.
Local Ltac2 unfold_is_accumulation_point_in (h : ident) := unfold is_accumulation_point in $h.
Ltac2 Notation "Expand" "the" "definition" "of" "accumulation" "point" cl(opt(seq("in", "(", ident, ")"))) := 
  expand_def_framework unfold_is_accumulation_point unfold_is_accumulation_point_in cl.


Notation "a 'is' 'an' '_isolated' 'point_'" := (is_isolated_point a) (at level 68).
Notation "a 'is' 'an' 'isolated' 'point'" := (is_isolated_point a) (at level 68, only parsing).
Local Ltac2 unfold_is_isolated_point    ()          := unfold is_isolated_point.
Local Ltac2 unfold_is_isolated_point_in (h : ident) := unfold is_isolated_point in $h.
Ltac2 Notation "Expand" "the" "definition" "of" "isolated" "point" cl(opt(seq("in", "(", ident, ")"))) := 
  expand_def_framework unfold_is_isolated_point unfold_is_isolated_point_in cl.


Notation "'_limit_' 'of' f 'in' a 'is' L" := (limit_in_point _ f a L) (at level 68).
Notation "'limit' 'of' f 'in' a 'is' L" := (limit_in_point _ f a L) (at level 68, only parsing).
Local Ltac2 unfold_limit_in_point    ()          := unfold limit_in_point.
Local Ltac2 unfold_limit_in_point_in (h : ident) := unfold limit_in_point in $h.
Ltac2 Notation "Expand" "the" "definition" "of" "limit" cl(opt(seq("in", "(", ident, ")"))) := 
  expand_def_framework unfold_limit_in_point unfold_limit_in_point_in cl.


Notation "f 'is' '_continuous_' 'in' a" := (is_continuous_in _ f a) (at level 68).
Notation "f 'is' 'continuous' 'in' a" := (is_continuous_in _ f a)  (at level 68, only parsing).
Local Ltac2 unfold_is_continuous_in    ()          := unfold is_continuous_in.
Local Ltac2 unfold_is_continuous_in_in (h : ident) := unfold is_continuous_in in $h.
Ltac2 Notation "Expand" "the" "definition" "of" "continuous" cl(opt(seq("in", "(", ident, ")"))) := 
  expand_def_framework unfold_is_continuous_in unfold_is_continuous_in_in cl.


Close Scope R_scope.
