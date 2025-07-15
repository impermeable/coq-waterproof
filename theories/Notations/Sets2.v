Require Import Libs.Sets.IndexedOperations.

Require Import Notations.Sets.

Notation "⋂_{ i Q } X_i" := (indexed_intersection Q%pfs (fun i => X_i)) (at level 30, i binder) : subset_scope.
(* ⋂_{i ∈ I}, X_i *)

Notation "⋃_{ i Q } X_i" := (indexed_union Q%pfs (fun i => X_i)) (at level 30, i binder).
(* ⋂_{i ∈ I}, X_i *)