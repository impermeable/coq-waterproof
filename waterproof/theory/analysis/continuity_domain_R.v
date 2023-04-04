Require Import Rbase.
Require Import Rbasic_fun.
Require Import Waterproof.AllTactics.
Require Import Waterproof.notations.notations.
Require Import Waterproof.load.
Module Import db_RealsAndIntegers := Waterproof.load.databases(RealsAndIntegers).
Require Import Waterproof.set_search_depth.To_5.

Open Scope R_scope.

(** Definitions *)
Definition is_accumulation_point (a : R) :=
  for all ε : R, (ε > 0) ⇒
    there exists x : R, 0 < |x - a| < ε.

Definition is_isolated_point (a : R) :=
  there exists ε : R, (ε > 0) ∧
    (for all x : R, |x - a| = 0 ∨ (ε ≤ |x - a|)).

Definition limit_in_point (f : R → R) (a : R) (q : R) :=
 for all ε : R, (ε > 0) ⇒
   there exists δ : R, (δ > 0) ∧
     (for all x : R,
       (0 < |x - a| < δ) ⇒ (|(f x) - q| < ε)).

Definition is_continuous_in (f : R → R) (a : R) :=
  ((is_accumulation_point a) ∧ (limit_in_point f a (f a))) ∨ (is_isolated_point a).


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


Notation "'_limit_' 'of' f 'in' a 'is' L" := (limit_in_point f a L) (at level 68).
Notation "'limit' 'of' f 'in' a 'is' L" := (limit_in_point f a L) (at level 68, only parsing).
Local Ltac2 unfold_limit_in_point    ()          := unfold limit_in_point.
Local Ltac2 unfold_limit_in_point_in (h : ident) := unfold limit_in_point in $h.
Ltac2 Notation "Expand" "the" "definition" "of" "limit" cl(opt(seq("in", "(", ident, ")"))) := 
  expand_def_framework unfold_limit_in_point unfold_limit_in_point_in cl.


Notation "f 'is' '_continuous_' 'in' a" := (is_continuous_in f a) (at level 68).
Notation "f 'is' 'continuous' 'in' a" := (is_continuous_in f a)  (at level 68, only parsing).
Local Ltac2 unfold_is_continuous_in    ()          := unfold is_continuous_in.
Local Ltac2 unfold_is_continuous_in_in (h : ident) := unfold is_continuous_in in $h.
Ltac2 Notation "Expand" "the" "definition" "of" "continuous" cl(opt(seq("in", "(", ident, ")"))) := 
  expand_def_framework unfold_is_continuous_in unfold_is_continuous_in_in cl.


Close Scope R_scope.