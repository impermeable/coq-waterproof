(** * Subsets

Authors:
    - Jim Portegies
    - Jelle Wemmenhove

Creation date: 25 Mar 2023.

This file derives additional lemmas about subsets.

This file is part of Waterproof-lib.

Waterproof-lib is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

Waterproof-lib is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with Waterproof-lib.  If not, see <https://www.gnu.org/licenses/>.
*)

Require Import Waterproof.notations.notations.
Require Import Waterproof.definitions.set_definitions.
Require Import Reals.
Open Scope R_scope.

Open Scope subset_scope.
Lemma left_in_closed_open {a b : R} : (a < b) -> (a : [a,b)).
Proof.
  intro a_lt_b.
  split.
  - apply Rle_refl.
  - exact a_lt_b.
Qed.
Lemma right_in_open_closed {a b : R} : (a < b) -> (b : (a,b]).
Proof.
  intro a_lt_b.
  split.
  - exact a_lt_b.
  - apply Rle_refl.
Qed.
Global Hint Resolve left_in_closed_open left_in_closed_open : subsets.
Close Scope subset_scope.
