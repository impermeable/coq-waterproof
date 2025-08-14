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
  fun y : Y => exists x : X, x ∈ U /\ y = g x.

(** * Basic Properties *)

(** Basic lemmas: membership in image (split into two directions) *)
Lemma in_function_image_intro {X Y : Type} (g : X -> Y) (U : subset X) (y : Y) :
  (∃ x ∈ X, x ∈ U /\ y = g x) -> y ∈ function_image g U.
Proof.
intro H.
unfold function_image.
rewrite exists_exists_in_iff in H.
exact H.
Qed.

Lemma in_function_image_elim {X Y : Type} (g : X -> Y) (U : subset X) (y : Y) :
  y ∈ function_image g U -> ∃ x ∈ X, x ∈ U /\ y = g x.
Proof.
intro H.
unfold function_image in H.
rewrite exists_exists_in_iff.
exact H.
Qed.

Lemma in_function_image_iff {X Y : Type} (g : X -> Y) (U : subset X) (y : Y) :
  y ∈ function_image g U <-> ∃ x ∈ X, x ∈ U /\ y = g x.
Proof.
split.
- exact (in_function_image_elim g U y).
- exact (in_function_image_intro g U y).
Qed.

