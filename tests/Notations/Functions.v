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
Require Import Waterproof.Notations.Functions.
Require Import Waterproof.Notations.Sets.
Require Import Waterproof.Notations.IndexedSets.
Require Import Waterproof.Chains.
Require Import Waterproof.Automation.
Require Import Waterproof.Libs.Functions.
Waterproof Enable Automation Intuition.
Waterproof Enable Automation Sets.

Require Import Sets.Ensembles.

Open Scope R_scope.
Open Scope subset_scope.


Context {X Y : Type}.

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
  It suffices to show that ∃ z ∈ U, y = g z.
  Choose z := x.
  { Indeed, z ∈ U. }
  We conclude that y = g z.
- We need to show that y ∈ g[V].
  It suffices to show that ∃ w ∈ V, y = g w.
  Choose w := x.
  { Indeed, w ∈ V. }
  We conclude that y = g w.
Qed.

Example example_3_1_39 (f : X → Y) (U : subset X) (V : subset Y) :
    (f[U] ⊂ V) ↔ (U ⊂ f⁻¹[V]).
Proof.
We show both directions.
+ We need to show that f [ U ] ⊂ V ⇨ U ⊂ f⁻¹[V].
  Assume that f[U] ⊂ V as (i).
  It suffices to show ∀ x ∈ U, x ∈ f⁻¹[V].
  Take x ∈ U.
  It holds that f(x) ∈ f[U].
  By (i) it holds that ∀ x ∈ f[U], x ∈ V.
  It holds that f(x) ∈ V.
  We conclude that x ∈ f⁻¹[V].
+ We need to show that (U ⊂ f⁻¹[V]) ⇨ f [U] ⊂ V.
  Assume that U ⊂ f⁻¹[V].
  It suffices to show ∀ y ∈ f[U], y ∈ V.
  Take y ∈ f[U].
  It holds that ∃ x ∈ U, y = f(x).
  Obtain such an x.
  It holds that ∀ x ∈ U, x ∈ f⁻¹[V].
  It holds that x ∈ f⁻¹[V].
  It holds that f(x) ∈ V.
  We conclude that y ∈ V.
Qed.
