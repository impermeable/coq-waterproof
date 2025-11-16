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

From Stdlib Require Import Sets.Ensembles.
From Stdlib Require Import Sets.Powerset.

Require Import Waterproof.Notations.Common.

Set Auto Template Polymorphism.

(* Record subset (X : Type) := as_subset { pred :> X -> Prop }.*)

Declare Scope subset_scope.

Notation "'subset' X " := (Ensemble X) (at level 20).

Definition as_subset (X : Type) (Q : X -> Prop) := Q.

Definition subset_type {X : Type} (A : subset X) := X.

Definition subset_in {X : Type} (A : subset X) (x : X) := A x.

Notation "'set_of_subsets' U" :=
  (subset (subset U)) (at level 50).

Definition empty {U} := Empty_set U.
Definition full {U} := Full_set U.
Notation "∅" :=
  (empty) : subset_scope.

Notation "'Ω'" :=
  (full) (at level 0) : subset_scope.

Notation "A ∩ B" :=
  (Intersection _ A B) (at level 45) : subset_scope.

Notation "A ∪ B" :=
  (Union _ A B) (at level 45) : subset_scope.

Notation "A \ B" :=
  (Setminus _ A B) (at level 45) : subset_scope.


Notation "x ∉ A" :=
  (~ In _ A x) (at level 50) : subset_scope.

Notation "A ⊂ B" :=
  (Included _ A B) (at level 45) : subset_scope.

(* Purposefully not formulated as `A and B are disjoint`, because that conflicts with
   Assume A and B. in case A and B can be interpreted as subsets. *)
Notation "A 'is' 'disjoint' 'from' B" :=
  (Disjoint _ A B) (at level 69) : subset_scope.

Notation "A 'is' 'empty'" :=
  (forall a : _, ~ In _ A a) (at level 1) : subset_scope.

Notation "A 'is' 'inhabited'" :=
  (exists a : _, In _ A a) (at level 1) : subset_scope.

Notation "｛ x : T | P ｝" :=
  (fun (x : T) ↦ P) (x at level 99) : subset_scope.

Notation " [ n ] " :=
  (fun (x : nat) ↦ x < n) : subset_scope.

Notation "𝒫( X )" := (Power_set _ X) : subset_scope.



(* Notation "x : A" := ((pred _ A) x) (at level 70, no associativity) : subset_scope. *)

Definition conv (T : Type) : T -> Prop := (fun x : T => True).
Coercion conv : Sortclass >-> Funclass.

Definition seal {T : Type} (Q : T -> Prop) (y : T) := Q y.



From Stdlib Require Import Reals.Reals.

Class ge_type (carrier : Type) := {
  ge_op : carrier -> carrier -> Prop
}.

#[export] Instance nat_ge_type : ge_type nat :=
  {ge_op := fun y z => ge z y}.

#[export] Instance R_ge_type : ge_type R :=
  {ge_op := fun y z => Rge z y}.

Class gt_type (carrier : Type) := {
  gt_op : carrier -> carrier -> Prop
}.

#[export] Instance nat_gt_type : gt_type nat :=
  {gt_op := fun y z => gt z y}.

#[export] Instance R_gt_type : gt_type R :=
  {gt_op := fun y z => Rgt z y}.

Class le_type (carrier : Type) := {
  le_op : carrier -> carrier -> Prop
}.

#[export] Instance nat_le_type : le_type nat :=
  {le_op := fun y z => le z y}.

#[export] Instance R_le_type : le_type R :=
  {le_op := fun y z => Rle z y}.

Class lt_type (carrier : Type) := {
  lt_op : carrier -> carrier -> Prop
}.

#[export] Instance nat_lt_type : lt_type nat :=
  {lt_op := fun y z => lt z y}.

#[export] Instance R_lt_type : lt_type R :=
  {lt_op := fun y z => Rlt z y}.

Class ne_type (carrier : Type) := {
  ne_op : carrier -> carrier -> Prop
}.

#[export] Instance nat_ne_type : ne_type nat :=
  {ne_op := fun y z => z <> y}.

#[export] Instance R_ne_type : ne_type R :=
  {ne_op := fun y z => z <> y}.


Declare Scope pred_for_subset_scope.

Delimit Scope pred_for_subset_scope with pfs.

Notation "∈ A" := (subset_in A) (at level 69, A at next level) : pred_for_subset_scope.

Notation "< y" :=  (lt_op y) (at level 69, y at next level) : pred_for_subset_scope.
Notation "≤ y" :=  (le_op y) (at level 69, y at next level) : pred_for_subset_scope.
Notation "> y" :=  (gt_op y) (at level 69, y at next level) : pred_for_subset_scope.
Notation "≥ y" :=  (ge_op y) (at level 69, y at next level) : pred_for_subset_scope.
Notation "≠ y" :=  (ne_op y) (at level 69, y at next level) : pred_for_subset_scope.

Notation "x ∈ A" := (subset_in A x) (at level 69, no associativity) : type_scope.
Notation "x ≥ y" := (ge_op y x) (at level 70, no associativity, only printing) : subset_scope.
Notation "x > y" := (gt_op y x) (at level 70, no associativity, only printing) : subset_scope.
Notation "x ≤ y" := (le_op y x) (at level 70, no associativity, only printing) : subset_scope.
Notation "x < y" := (lt_op y x) (at level 70, no associativity, only printing) : subset_scope.

Notation "∃ x , P" := (exists x, P)
  (at level 200, x binder, right associativity) : type_scope.

Notation "'there' 'exists' x , P" := (exists x, P)
  (at level 200, x binder, right associativity, only parsing) : type_scope.

Notation "∀ x , P" := (forall x, P)
  (at level 200, x binder, right associativity) : type_scope.

Notation "'for' 'all' x , P" := (forall x, P)
  (at level 200, x binder, right associativity, only parsing) : type_scope.

Notation "'∃' x Q , P" :=
  (seal (fun z : subset_type ((Q)%pfs) -> Prop => exists x : (subset_type ((Q)%pfs)), z x /\ P) Q%pfs)
  (at level 200, x binder, right associativity) : subset_scope.

Notation "'there' 'exists' x Q , P" :=
  (seal (fun z : subset_type ((Q)%pfs) -> Prop => exists x : (subset_type ((Q)%pfs)), z x /\ P) Q%pfs)
  (at level 200, x binder, right associativity, only parsing) : subset_scope.

Notation "'∀' x Q , P" :=
  (seal (fun z : subset_type ((Q)%pfs) -> Prop => forall x : (subset_type ((Q)%pfs)), z x -> P) Q%pfs)
  (at level 200, x binder, right associativity) : subset_scope.

Notation "'for' 'all' x Q , P" :=
  (seal (fun z : subset_type ((Q)%pfs) -> Prop => forall x : (subset_type ((Q)%pfs)), z x -> P) Q%pfs)
  (at level 200, x binder, right associativity, only parsing) : subset_scope.

Lemma mem_subset_full_set {T : Type} (x : T) : (x ∈ T).
Proof.
unfold subset_in, conv, as_subset; exact I.
Qed.

Notation "{ x ∈ X | P }" := (fun x => subset_in X x ∧ P)
  (at level 0, x binder, X at level 99) : subset_scope.

Notation "{ x , y }" := (fun a => a = x ∨ a = y) (at level 0, x at level 99, y at level 99) : subset_scope.


Open Scope subset_scope.

Definition unique_exists {T : Type} (Q : subset T) (P : T -> Prop) :=
  (∃ x Q, (P x)) ∧ (∀ x Q, ∀ y Q, (P x) ∧ (P y) ⇒ x = y).

Notation "∃! x Q , P" := (unique_exists (Q%pfs) (fun x : (subset_type Q%pfs) => P)) (at level 199, x binder, right associativity) : subset_scope.

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

Notation "A 'is' 'empty'" :=
  (¬ (∃ x, x ∈ A)) (at level 1).
