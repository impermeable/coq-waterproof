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

(* Record subset (X : Type) := as_subset { pred :> X -> Prop }.*)

Definition subset (X : Type) := X -> Prop.
Definition as_subset (X : Type) (Q : X -> Prop) := Q.

Definition subset_type {X : Type} (A : subset X) := X.

Definition subset_in {X : Type} (A : subset X) (x : X) := A x.

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
(* Notation "x : A" := ((pred _ A) x) (at level 70, no associativity) : subset_scope. *)

Definition conv (T : Type) : subset T := as_subset T (fun x : T => True).
Coercion conv : Sortclass >-> subset.

Definition seal {T : Type} (Q : T -> Prop) (y : T) := Q y.

Notation "x ∈ A" := (subset_in A x) (at level 70, no associativity) : type_scope.

Notation "∃ x , P" := (exists x, P)
  (at level 200, x binder, right associativity) : type_scope.

Notation "'there' 'exists' x , P" := (exists x, P)
  (at level 200, x binder, right associativity) : type_scope.

Notation "∀ x , P" := (forall x, P)
  (at level 200, x binder, right associativity) : type_scope.

Notation "'for' 'all' x , P" := (forall x, P)
  (at level 200, x binder, right associativity) : type_scope.

Notation "∃ x ∈ A , P " :=
  (seal (fun B : subset (subset_type A) => (exists x,
    (x ∈ B) /\ P)) A)
  (at level 200, x binder, right associativity(*,
  format "'[ ' '[ ' ∃  x  ∈  A ']' , '//'  P ']'"*)) : subset_scope.

Notation "∀ x ∈ A , P" :=
  (seal (fun B : subset (subset_type A) =>
    forall x, (x ∈ B) -> P ) A)
  (at level 200, x binder, right associativity (*,
  format "'[ ' '[ ' ∀  x  ∈  A ']' , '//'  P ']'"*)) : subset_scope.

(* Notation "∃ x '>' y , P" :=
  (seal (fun z => exists x, x > z /\ P) y)
  (at level 200, x binder, right associativity) : nat_scope.

Notation "∀ x '>' y , P" :=
  (seal (fun z => forall x, x > z -> P) y)
  (at level 200, x binder, right associativity) : nat_scope.

Notation "∃ x '≥' y , P" :=
  (seal (fun z => exists x, x >= z /\ P) y)
  (at level 200, x binder, right associativity) : nat_scope.

Notation "∀ x '≥' y , P" :=
  (seal (fun z => forall x, x >= z -> P) y)
  (at level 200, x binder, right associativity) : nat_scope.*)

Declare Scope wp_scope.

Require Import Coq.Reals.Reals.

Class ge_type (carrier : Type) := {
  ge_op : carrier -> carrier -> Prop
}.

#[export] Instance nat_ge_type : ge_type nat :=
  {ge_op := ge}.

#[export] Instance R_ge_type : ge_type R :=
  {ge_op := Rge}.

Class gt_type (carrier : Type) := {
  gt_op : carrier -> carrier -> Prop
}.

#[export] Instance nat_gt_type : gt_type nat :=
  {gt_op := gt}.

#[export] Instance R_gt_type : gt_type R :=
  {gt_op := Rgt}.

Notation "x ≥ y" := (ge_op x y) (at level 70, no associativity, only printing) : subset_scope.
Notation "x > y" := (gt_op x y) (at level 70, no associativity, only printing) : subset_scope.

Notation "∃ x '>' y , P" :=
  (seal (fun z => exists x, gt_op x z /\ P) y)
  (at level 200, x binder, right associativity) : subset_scope.

Notation "∀ x '>' y , P" :=
  (seal (fun z => forall x, gt_op x z -> P) y)
  (at level 200, x binder, right associativity) : subset_scope.

Notation "∃ x '≥' y , P" :=
  (seal (fun z => exists x, ge_op x z /\ P) y)
  (at level 200, x binder, right associativity) : subset_scope.

Notation "∀ x '≥' y , P" :=
  (seal (fun z => forall x, ge_op x z -> P) y)
  (at level 200, x binder, right associativity) : subset_scope.


Close Scope wp_scope.

Open Scope R_scope.

(* Notation "∃ x '>' y , P" :=
  (seal (fun z => exists x, x > z /\ P) y)
  (at level 200, x binder, right associativity) : R_scope.

Notation "∀ x '>' y , P" :=
  (seal (fun z => forall x, x > z -> P) y)
  (at level 200, x binder, right associativity) : R_scope.

Notation "∃ x '≥' y , P" :=
  (seal (fun z => exists x, x >= z /\ P) y)
  (at level 200, x binder, right associativity) : R_scope.

Notation "∀ x '≥' y , P" :=
  (seal (fun z => forall x, x >= z -> P) y)
  (at level 200, x binder, right associativity) : R_scope.*)

Close Scope R_scope.

Lemma mem_subset_full_set {T : Type} (x : T) : (x ∈ T).
Proof.
unfold subset_in, conv, as_subset; exact I.
Qed.

Open Scope subset_scope.

Lemma forall_forall_in_iff (T : Type) (Q : T -> Prop) :
  (∀ x ∈ T, Q x) <-> ∀ x, Q x.
Proof.
  unfold seal, subset_in, conv, as_subset.
  split; auto.
Qed.

Lemma exists_exists_in_iff (T : Type) (Q : T -> Prop) :
  (∃ x ∈ T, Q x) <-> ∃ x, Q x.
Proof.
  unfold seal, subset_in, conv, as_subset.
  split.
  * intro H. destruct H as [x [wx1 wx2]].
    exists x. exact wx2.
  * intro H. destruct H as [x wx].
    exists x. auto.
Qed.

Close Scope subset_scope.
Close Scope R_scope.
Close Scope wp_scope.
