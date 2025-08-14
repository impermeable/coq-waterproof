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

Require Import Waterproof.Notations.Common.
Require Import Waterproof.Notations.Sets.

Require Import Sets.Ensembles.

Open Scope subset_scope.

(** * Function Image *)

(** 
  We formalize the notion of the image of a function. Given a function `g : X → Y` 
  and a subset `U`, the image of `U` under `g` is the set of all values `y` such 
  that there exists some `x ∈ U` with `y = g(x)`.
*)

Definition function_image {X Y : Type} (g : X -> Y) (U : subset X) : subset Y :=
  fun y : Y => ∃ x ∈ U, y = g x.

(** * Basic Properties *)

(** Basic lemmas: membership in image (split into two directions) *)
Lemma in_function_image_intro {X Y : Type} (g : X -> Y) (U : subset X) (y : Y) :
  (∃ x ∈ U, y = g x) -> y ∈ function_image g U.
Proof.
intro H.
unfold function_image.
exact H.
Qed.

Lemma in_function_image_elim {X Y : Type} (g : X -> Y) (U : subset X) (y : Y) :
  y ∈ function_image g U -> ∃ x ∈ U, y = g x.
Proof.
intro H.
unfold function_image in H.
exact H.
Qed.

Lemma in_function_image_iff {X Y : Type} (g : X -> Y) (U : subset X) (y : Y) :
  y ∈ function_image g U <-> ∃ x ∈ U, y = g x.
Proof.
split.
- exact (in_function_image_elim g U y).
- exact (in_function_image_intro g U y).
Qed.

(** * Function Preimage *)

(** 
  We formalize the notion of the preimage of a function. Given a function `f : X → Y` 
  and a subset `V`, the preimage of `V` under `f` is the set of all values `x` such 
  that there exists some `y ∈ V` with `f(x) = y`.
*)

Definition function_preimage {X Y : Type} (f : X -> Y) (V : subset Y) : subset X :=
  fun x : X => ∃ y ∈ V, f x = y.

(** * Basic Properties for Preimage *)

(** Basic lemmas: membership in preimage (split into two directions) *)
Lemma in_function_preimage_intro {X Y : Type} (f : X -> Y) (V : subset Y) (x : X) :
  (∃ y ∈ V, f x = y) -> x ∈ function_preimage f V.
Proof.
intro H.
unfold function_preimage.
exact H.
Qed.

Lemma in_function_preimage_elim {X Y : Type} (f : X -> Y) (V : subset Y) (x : X) :
  x ∈ function_preimage f V -> ∃ y ∈ V, f x = y.
Proof.
intro H.
unfold function_preimage in H.
exact H.
Qed.

Lemma in_function_preimage_iff {X Y : Type} (f : X -> Y) (V : subset Y) (x : X) :
  x ∈ function_preimage f V <-> ∃ y ∈ V, f x = y.
Proof.
split.
- exact (in_function_preimage_elim f V x).
- exact (in_function_preimage_intro f V x).
Qed.

Lemma preimage_of_mem {X Y : Type} (f : X -> Y) (V : subset Y) (x : X) :
  f x ∈ V -> x ∈ function_preimage f V.
Proof.
intro H.
unfold function_preimage.
exists (f x).
split.
- exact H.
- reflexivity.
Qed.

Lemma mem_of_preimage {X Y : Type} (f : X -> Y) (V : subset Y) (x : X) :
  x ∈ function_preimage f V -> f x ∈ V.
Proof.
intro H.
unfold function_preimage in H.
destruct H as [y [H_y_in_V H_fx_eq_y]].
rewrite H_fx_eq_y.
exact H_y_in_V.
Qed.


