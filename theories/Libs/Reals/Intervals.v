Require Import Notations.Common.
Require Import Notations.Sets.
Require Import Notations.Reals.

Open Scope R_scope.

Inductive is_interval (A : subset ℝ) : Prop :=
    | Closed : forall a b : ℝ, A = [a, b] ⇒ is_interval A
    | Open : forall a b : ℝ, A = (a, b) ⇒ is_interval A
    | Closed_Open : forall a b : ℝ, A = [a, b) ⇒ is_interval A
    | Open_Closed : forall a b : ℝ, A = (a, b] ⇒ is_interval A.
