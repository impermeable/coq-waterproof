Require Import Qreals.
Require Import Coq.Reals.Reals.
Require Import Rbase.
Require Import Rfunctions.
Require Import SeqSeries.
Require Import Rtrigo.
Require Import Ranalysis.
Require Import Integration.
Require Import micromega.Lra.
Require Import Max.

Record subset (X : Type) := as_subset { pred :> X -> Prop }.

(** ** Standard mathematical function notation. *)
Notation " f ( x , .. , y )" := (.. (f x) .. y) 
  (at level 10,
  format "f '(' x ,  .. ,  y ')'") : type_scope.

(** ** Quantifiers
  Allow unicode characters ∀ and ∃ for readability.
*)
Notation "'for' 'all' x .. y , P" := (forall x, .. (forall y, P) ..)
  (at level 200, x binder, y binder, right associativity,
  format "'[ ' '[ ' for  all  x .. y ']' , '//'  P ']'") : type_scope.

Notation "∀ x .. y , P" := (forall x, .. (forall y, P) ..)
  (at level 200, x binder, y binder, right associativity,
  only parsing) : type_scope.

Notation "'there' 'exists' x .. y , P " := (exists x, .. (exists y, P) ..)
  (at level 200, x binder, y binder, right associativity,
  format "'[ ' '[ ' there  exists  x .. y ']' , '//'  P ']'") : type_scope.

Notation "∃ x .. y , P " := (exists x, .. (exists y, P) ..)
  (at level 200, x binder, y binder, right associativity,
  only parsing) : type_scope.

Notation "'fun' x .. y '↦' t" := (fun x => .. (fun y => t) ..)
  (at level 200, x binder, y binder, right associativity,
  format "'[ ' '[ ' 'fun' x .. y ']' '↦' '/' t ']'") : type_scope.

(** ** Set symbols, implications
  The following notations deal with sets.
*)
Notation "x ∨ y" := (x \/ y) (at level 85, right associativity) : type_scope.
Notation "x ∧ y" := (x /\ y) (at level 80, right associativity) : type_scope.

Notation "x → y" := (x -> y) (at level 99, y at level 200, right associativity, only parsing): type_scope.

Notation "x ⇒ y" := (x -> y) (at level 99, y at level 200, right associativity, only parsing): type_scope.

Notation "x ⇨ y" := (x -> y) (at level 99, y at level 200, right associativity): type_scope.

Notation "x ↔ y" := (x <-> y) (at level 95, no associativity): type_scope.
Notation "x ⇔ y" := (x <-> y) (at level 95, no associativity): type_scope.
Notation "¬ x" := (~x) (at level 75, right associativity) : type_scope.
Notation "'Show' 'a' 'contradiction' 'by:' '(1)' 'Showing' 'that' 'both' 'P' 'and' '¬P' 'hold' 'for' 'some' 'statement' 'P.' '(2)' 'Writing' '‘Contradiction.‘' 'or' '‘↯.‘.'" := (False) 
  (only printing, format "'[ ' Show  a  contradiction  by: ']' '//' (1)  Showing  that  both  P  and  ¬P  hold  for  some  statement  P. '//' (2)  Writing  ‘Contradiction.‘  or  ‘↯.‘.").

(* TODO: the below definition doesn't work very nicely *)
Notation "x ↦ y" := (fun x => y) (at level 0).

(** ** (In)equalities
  Allowing unicode characters for uniqualities.
*)
Notation "x ≠ y" := (x <> y) (at level 70) : type_scope.
Notation "x ≤ y" := (le x y) (at level 70, no associativity) : nat_scope.
Notation "x ≥ y" := (ge x y) (at level 70, no associativity) : nat_scope.
Notation "x ≤ y" := (x <= y)%R (at level 70, no associativity) : R_scope.
Notation "x ≥ y" := (x >= y)%R (at level 70, no associativity) : R_scope.

Open Scope nat_scope.
Open Scope R_scope.

(** ** Scopes and coercions *)
Notation "'ℕ'" := (nat).
Notation "'ℤ'" := (Z).
Notation "'ℚ'" := (Q).
Notation "'ℝ'" := (R).

(* We use coercions to get around writing INR and IZR *)
Coercion INR: nat >-> R.
Coercion IZR: Z >-> R.
Coercion Q2R: Q >-> R.

(** ** Sequences *)
Definition converges_to (a : ℕ → ℝ) (c : ℝ) :=
  ∀ ε : ℝ, ε > 0 ⇒
    ∃ N : ℕ, ∀ n : ℕ, (n ≥ N)%nat ⇒
      R_dist (a n) c < ε.

Notation "a ⟶ c" := (converges_to a c) (at level 20).

Definition cv_implies_cv_abs_to_l_abs := cv_cvabs.

(** * Real numbers

  We have to take care with the associative level.
  When using this in rewrites, $<$, $>$, etc. should bind stronger.
*)

Declare Scope extra.

Notation "| x |" := (Rabs x) (at level 65, x at next level, format "| x |").
Notation "｜ x - y ｜" := (R_dist x y) (at level 65, x at level 48, y at level 48, format "｜ x  -  y ｜") : extra.


(** ** Sums and series *)
Notation "'Σ' Cn 'equals' x" := (infinite_sum Cn x) (at level 50).

Definition finite_triangle_inequalty := sum_f_R0_triangle.

(** ** Subsets and intervals*)
Notation "[ a , b ]" := (as_subset R (fun x => (a <= x <= b))).
Notation "[ a , b )" := (as_subset R (fun x => (a <= x <  b))).
Notation "( a , b ]" := (as_subset R (fun x => (a <  x <= b))).
Notation "( a , b )" := (as_subset R (fun x => (a <  x <  b))).

Close Scope nat_scope.

Close Scope R_scope.

Declare Scope subset_scope.
Notation "x : A" := ((pred _ A) x) (at level 70, no associativity) : subset_scope.
