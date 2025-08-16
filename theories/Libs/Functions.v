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

Definition image {X Y : Type} (g : X -> Y) (U : subset X) : subset Y :=
  fun y : Y => ∃ x ∈ U, y = g x.

(** * Basic Properties *)

(** Basic lemmas: membership in image (split into two directions) *)
Lemma in_image_intro {X Y : Type} (g : X -> Y) (U : subset X) (y : Y) :
  (∃ x ∈ U, y = g x) -> y ∈ image g U.
Proof.
intro H.
unfold image.
exact H.
Qed.

Lemma in_image_elim {X Y : Type} (g : X -> Y) (U : subset X) (y : Y) :
  y ∈ image g U -> ∃ x ∈ U, y = g x.
Proof.
intro H.
unfold image in H.
exact H.
Qed.

Lemma in_image_iff {X Y : Type} (g : X -> Y) (U : subset X) (y : Y) :
  y ∈ image g U <-> ∃ x ∈ U, y = g x.
Proof.
split.
- exact (in_image_elim g U y).
- exact (in_image_intro g U y).
Qed.

(** * Function Preimage *)

(** 
  We formalize the notion of the preimage of a function. Given a function `f : X → Y` 
  and a subset `V`, the preimage of `V` under `f` is the set of all values `x` such 
  that there exists some `y ∈ V` with `f(x) = y`.
*)

Definition preimage {X Y : Type} (f : X -> Y) (V : subset Y) : subset X :=
  fun x : X => ∃ y ∈ V, f x = y.

(** * Basic Properties for Preimage *)

(** Basic lemmas: membership in preimage (split into two directions) *)
Lemma in_preimage_intro {X Y : Type} (f : X -> Y) (V : subset Y) (x : X) :
  (∃ y ∈ V, f x = y) -> x ∈ preimage f V.
Proof.
intro H.
unfold preimage.
exact H.
Qed.

Lemma in_preimage_elim {X Y : Type} (f : X -> Y) (V : subset Y) (x : X) :
  x ∈ preimage f V -> ∃ y ∈ V, f x = y.
Proof.
intro H.
unfold preimage in H.
exact H.
Qed.

Lemma in_preimage_iff {X Y : Type} (f : X -> Y) (V : subset Y) (x : X) :
  x ∈ preimage f V <-> ∃ y ∈ V, f x = y.
Proof.
split.
- exact (in_preimage_elim f V x).
- exact (in_preimage_intro f V x).
Qed.

Lemma preimage_of_mem {X Y : Type} (f : X -> Y) (V : subset Y) (x : X) :
  f x ∈ V -> x ∈ preimage f V.
Proof.
intro H.
unfold preimage.
exists (f x).
split.
- exact H.
- reflexivity.
Qed.

Lemma mem_of_preimage {X Y : Type} (f : X -> Y) (V : subset Y) (x : X) :
  x ∈ preimage f V -> f x ∈ V.
Proof.
intro H.
unfold preimage in H.
destruct H as [y [H_y_in_V H_fx_eq_y]].
rewrite H_fx_eq_y.
exact H_y_in_V.
Qed.

(** * Injective Functions *)

(** 
  We formalize the notion of injective (one-to-one) functions. A function `f : X → Y` 
  is injective if for all `a, b ∈ X`, if `f(a) = f(b)` then `a = b`.
  In other words, distinct elements in the domain map to distinct elements in the codomain.
*)

Definition injective {X Y : Type} (f : X -> Y) : Prop :=
  ∀ a ∈ X, ∀ b ∈ X, f a = f b → a = b.

(** * Basic Properties of Injective Functions *)

(** If f is injective and f(a) = f(b), then a = b *)
Lemma injective_elim {X Y : Type} (f : X -> Y) (a b : X) :
  injective f → f a = f b → a = b.
Proof.
intros H_inj H_eq.
apply H_inj.
- (* Prove a ∈ X *) 
  apply mem_subset_full_set.
- (* Prove b ∈ X *)
  apply mem_subset_full_set.
- (* Use the equality *)
  exact H_eq.
Qed.

(** * Surjective Functions *)

(** 
  We formalize the notion of surjective (onto) functions. A function `f : X → Y` 
  is surjective if for all `y ∈ Y`, there exists some `x ∈ X` such that `f(x) = y`.
  In other words, every element in the codomain is the image of at least one element 
  in the domain.
*)

Definition surjective {X Y : Type} (f : X -> Y) : Prop :=
  ∀ y ∈ Y, ∃ x ∈ X, f x = y.

(** * Basic Properties of Surjective Functions *)

(** If f is surjective and y ∈ Y, then there exists x ∈ X such that f(x) = y *)
Lemma surjective_elim {X Y : Type} (f : X -> Y) (y : Y) :
  surjective f → ∃ x ∈ X, f x = y.
Proof.
intro H_surj.
apply H_surj.
(* Prove y ∈ Y *)
apply mem_subset_full_set.
Qed.

(** * Bijective Functions *)

(** 
  We formalize the notion of bijective functions. A function `f : X → Y` 
  is bijective if it is both injective and surjective.
  In other words, f is a one-to-one correspondence between X and Y.
*)

Definition bijective {X Y : Type} (f : X -> Y) : Prop :=
  injective f ∧ surjective f.

(** * Basic Properties of Bijective Functions *)

(** If f is bijective, then f is injective *)
Lemma bijective_is_injective {X Y : Type} (f : X -> Y) :
  bijective f → injective f.
Proof.
intro H_bij.
unfold bijective in H_bij.
destruct H_bij as [H_inj _].
exact H_inj.
Qed.

(** If f is bijective, then f is surjective *)
Lemma bijective_is_surjective {X Y : Type} (f : X -> Y) :
  bijective f → surjective f.
Proof.
intro H_bij.
unfold bijective in H_bij.
destruct H_bij as [_ H_surj].
exact H_surj.
Qed.

(** A function is bijective if and only if it is both injective and surjective *)
Lemma bijective_iff {X Y : Type} (f : X -> Y) :
  bijective f ↔ (injective f ∧ surjective f).
Proof.
unfold bijective.
split; intro H; exact H.
Qed.

Definition composition {X Y Z : Type} (f : X -> Y) (g : Y -> Z) : X -> Z :=
  fun x => g (f x).

Definition left_inverse {X Y : Type} (f : X -> Y) (g : Y -> X) : Prop := composition f g = id.



Definition has_left_inverse {X Y : Type} (f : X -> Y) : Prop := ∃ (g : Y -> X), left_inverse f g.

(** * Lemmas for Left Inverse *)

(** If g is a left inverse of f, then g ∘ f = id pointwise *)
Lemma left_inverse_elim {X Y : Type} (f : X -> Y) (g : Y -> X) :
  left_inverse f g → (∀ x ∈ X, g (f x) = x).
Proof.
intro H.
unfold left_inverse in H.
intro x.
intro H_x_in_X.
(* From composition f g = id, we get (composition f g) x = id x *)
assert (H_point : (composition f g) x = id x).
{ rewrite H. reflexivity. }
unfold composition in H_point.
exact H_point.
Qed.
