(******************************************************************************)
(*                  This file is part of Waterproof-lib.                     *)
(*                                                                            *)
(*   Waterproof-lib is free software: you can redistribute it and/or modify  *)
(*    it under the terms of the GNU General Public License as published by   *)
(*     the Free Software Foundation, either version 3 of the License, or     *)
(*                    (at your option) any later version.                    *)
(*                                                                            *)
(*     Waterproof-lib is distributed in the hope that it will be useful,     *)
(*      but WITHOUT ANY WARRANTY; without even the implied warranty of       *)
(*       MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the        *)
(*               GNU General Public License for more details.                *)
(*                                                                            *)
(*     You should have received a copy of the GNU General Public License     *)
(*   along with Waterproof-lib. If not, see <https://www.gnu.org/licenses/>. *)
(*                                                                            *)
(******************************************************************************)

Require Import Waterproof.Tactics.
Require Import Waterproof.Notations.Common.
Require Import Waterproof.Notations.Sets.
Require Import Waterproof.Notations.IndexedSets.
Require Import Waterproof.Notations.Reals.
Require Import Waterproof.Notations.RealsWithSubsets.
Require Import Waterproof.Chains.
Require Import Waterproof.Automation.
Require Import Waterproof.Libs.Functions.
Require Import Waterproof.Libs.Notations.Functions.
Waterproof Enable Automation Intuition.
Waterproof Enable Automation Sets.
Waterproof Enable Automation RealsAndIntegers.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Require Import Coq.micromega.Lia.

Require Import Sets.Ensembles.

Open Scope R_scope.
Open Scope subset_scope.


Context {X Y : Type}.

(** ** Example 3.1.35: g[U ∩ V] ⊆ g[U] ∩ g[V] *)

Example example_3_1_35 (g : X → Y) (U V : subset X) :
  g[U ∩ V] ⊂ (g[U] ∩ g[V]).
Proof.
It suffices to show that ∀ y ∈ g[U ∩ V], y ∈ g[U] ∩ g[V].
Take y ∈ g[U ∩ V].
It holds that ∃ x : X, In X (U ∩ V) x ∧ y = g x.
Obtain such an x.
It holds that x ∈ U ∧ x ∈ V.
It suffices to show that y ∈ g[U] ∧ y ∈ g[V].
We show both statements.
- We need to show that y ∈ g[U].
  It suffices to show that ∃ z ∈ X, z ∈ U ∧ y = g z.
  Choose z := x.
  { Indeed, z ∈ X. }
  We conclude that z ∈ U ∧ y = g z.
- We need to show that y ∈ g[V].
  It suffices to show that ∃ w ∈ X, w ∈ V ∧ y = g w.
  Choose w := x.
  { Indeed, w ∈ X. }
  We conclude that w ∈ V ∧ y = g w.
Qed.

