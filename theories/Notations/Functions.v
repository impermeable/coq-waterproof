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

Require Import Waterproof.Libs.Functions.
Require Import Waterproof.Notations.Sets.

(** Declare a scope for function-related notations *)
Declare Scope function_scope.

(** * Notations for function images and preimages *)

(** The notation g[U] for the image of set U under function g *)
Notation "g [ U ]" := (image g U) (at level 10) : function_scope.

(** The notation f⁻¹[V] for the preimage of set V under function f *)
Notation "f ⁻¹[ V ]" := (preimage f V) (at level 10) : function_scope.

(** * Function Composition *)
(** The notation g ∘ f for the composition of functions g and f *)
(** This matches the mathematical convention where (g ∘ f)(x) = g(f(x)) *)
Notation "g ∘ f" := (composition f g) (at level 40, left associativity) : function_scope.

Notation "f 'is' 'injective'" := (injective f) (at level 68) : function_scope.

Notation "f 'is' 'surjective'" := (surjective f) (at level 68) : function_scope.

Notation "f 'is' 'bijective'" := (bijective f) (at level 68) : function_scope.

Notation "f 'has' 'a' 'left' 'inverse'" := (has_left_inverse f) (at level 68) : function_scope.

Notation "f 'is' 'a' 'left' 'inverse' 'of' g" := (left_inverse g f) (at level 68) : function_scope.

Notation "f 'has' 'a' 'right' 'inverse'" := (has_right_inverse f) (at level 68) : function_scope.

Notation "f 'is' 'a' 'right' 'inverse' 'of' g" := (right_inverse g f) (at level 68) : function_scope.

Notation "f 'has' 'an' 'inverse'" := (has_inverse f) (at level 68) : function_scope.

Notation "f 'is' 'an' 'inverse' 'of' g" := (inverse g f) (at level 68) : function_scope.

