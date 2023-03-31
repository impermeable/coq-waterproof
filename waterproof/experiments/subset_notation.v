Require Import Classical_Prop.

Record subset (X : Type) := as_subset { pred :> X -> Prop }.
Notation "x : A" := ((pred _ A) x) (at level 70, no associativity) : type_scope.



(*Definition eqv_pred {X : Type} {P : X -> Prop} (x : X) :
  (pred (as_subset X P)) x <-> P x.
Proof. reflexivity. Qed.
#[export] Hint Resolve eqv_pred : subsets.*)

Require Import Reals.
Require Import Lra.
Open Scope R_scope.

Variable P : R -> Prop.
Definition A := as_subset R P.

Variable x : R.
Check (x : A).
Check (is_lub A).


Notation "[ a , b ]" := (as_subset R (fun x => (a <= x <= b))).

Check (x : [0,1]).


Goal is_upper_bound [0,1] 1.
Proof.
  unfold is_upper_bound.
  intro a.
  intro a_in_interval.
  assert (0 <= a <= 1) by auto.
  lra.
Qed.

Goal 1/2 : [0,1].
Proof.
  enough (0 <= 1/2 <= 1) by auto.
  lra.
Qed.




(* (Bad) alternative *)
(* Clashes with default x : A notation on forall or exists statements. *)
Notation "x ∈ A" := ((pred _ A) x) (at level 70, no associativity) : type_scope.
Check (x ∈ [0,1]).

