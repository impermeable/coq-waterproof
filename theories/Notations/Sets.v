(******************************************************************************)
(*                  This file is part of Waterproof-lib.                      *)
(*                                                                            *)
(*   Waterproof-lib is free software: you can redistribute it and/or modify   *)
(*    it under the terms of the GNU General Public License as published by    *)
(*     the Free Software Foundation, either version 3 of the License, or      *)
(*                    (at your option) any later version.                     *)
(*                                                                            *)
(*     Waterproof-lib is distributed in the hope that it will be useful,      *)
(*      but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*       MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the         *)
(*               GNU General Public License for more details.                 *)
(*                                                                            *)
(*     You should have received a copy of the GNU General Public License      *)
(*   along with Waterproof-lib. If not, see <https://www.gnu.org/licenses/>.  *)
(*                                                                            *)
(******************************************************************************)

Require Import Sets.Ensembles.

Require Import Notations.Common.

Set Auto Template Polymorphism.
Record subset (X : Type) := as_subset { pred :> X -> Prop }.

Notation "'set_of_subsets' U" :=
  (Ensemble (Ensemble U)) (at level 50).

Definition empty {U} := Empty_set U.
Definition full {U} := Full_set U.
Notation "∅" :=
  (empty).

Notation "'Ω'" :=
  (full) (at level 0).

Notation "A ∩ B" :=
  (Intersection _ A B) (at level 45).

Notation "A ∪ B" :=
  (Union _ A B) (at level 45).

Notation "A \ B" :=
  (Setminus _ A B) (at level 45).

(* Notation "x ∈ A" :=
  (In _ A x) (at level 50). *)

Notation "x ∉ A" :=
  (~ In _ A x) (at level 50).

Notation "A ⊂ B" :=
  (Included _ A B) (at level 45).

Notation "A 'and' B 'are' 'disjoint'" :=
  (Disjoint _ A B) (at level 50).

Notation "｛ x : T | P ｝" :=
  (fun (x : T) ↦ P) (x at level 99).

Declare Scope subset_scope.
Notation "x : A" := ((pred _ A) x) (at level 70, no associativity) : subset_scope.

(* Definition conv (T : Type) : (T -> Prop) := as_subset _ (fun x => True).
Coercion conv : Sortclass >-> Funclass.*)

Notation "x ∈ A" := ((pred _ A) x) (at level 70, no associativity) : type_scope.

(* Notation "∃ x .. y ∈ A , P " :=
  (exists x, (x ∈ A) /\ .. (exists y, (y ∈ A) /\ P) ..)
  (at level 200, x binder, y binder, right associativity,
  format "'[ ' '[ ' ∃  x .. y  ∈  A ']' , '//'  P ']'") : type_scope.

Notation "∀ x .. y ∈ A , P" :=
  (forall x, (x ∈ A) -> .. (forall y, (y ∈ A) -> P) .. )
  (at level 200, x binder, y binder, A at level 20, right associativity,
  format "'[ ' '[ ' ∀  x .. y  ∈  A ']' , '//'  P ']'") : type_scope.*)

(* Local Parameter A : nat -> Prop.
Definition B := as_subset _ A.

Goal forall x : nat, forall y : nat, B x -> y = 0.
Abort. *)

Notation "∃ x , P" := (exists x, P)
  (at level 200, x binder, right associativity,
  only parsing) : type_scope.

Notation "∀ x , P" := (forall x, P)
  (at level 200, x binder, right associativity,
  only parsing) : type_scope.

Notation "∃ x ∈ A , P " :=
  (exists x, (x ∈ A) /\ P)
  (at level 200, x binder, right associativity,
  format "'[ ' '[ ' ∃  x  ∈  A ']' , '//'  P ']'") : subset_scope.

Notation "∀ x ∈ A , P" :=
  (forall x, (x ∈ A) -> P )
  (at level 200, x binder, right associativity,
  format "'[ ' '[ ' ∀  x  ∈  A ']' , '//'  P ']'") : subset_scope.

(* Notation "∀ x .. y ∈ , P" :=
  (forall x, x = 0 -> .. (forall y, y = 0 -> P) .. )
  (at level 200, x binder, y binder, right associativity,
  format "'[ ' '[ ' ∀  x .. y  ∈  ']' , '//'  P ']'") : type_scope. *)

(* Goal forall x : nat, forall y : nat, y = 0 -> True.
Abort.*)

(* Notation "'mf' x .. y , P" :=
  (forall x, x = 0 ∧ .. (forall y, y = 0 ∧ P) .. )
  (at level 200, x binder, y binder, right associativity).

Notation "'mf2' x , P" :=
  (forall x, x = 0 -> P )
  (at level 200, x binder,right associativity).

Goal forall x : nat, 3 = 0 ∧ x = 0.

Local Parameter A : nat -> Prop.
Definition B := as_subset _ A.

Goal forall k : nat, forall l : nat, k ∈ B -> l = 0.
Abort.

Notation "'myfor' x , P" :=
  (forall x, x ∈ B /\ P) (at level 200, x binder).

Goal forall x : nat, 0 ∈ B /\ x = 0.

Goal forall k : nat, 3 ∈ B -> k = 0.

Goal ∃ k : nat, 3 ∈ B ∧ k = 0.
Unset Printing Notations.*)