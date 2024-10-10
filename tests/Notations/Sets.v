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

Require Import Waterproof.Notations.Sets.

Open Scope nat_scope.
Goal ∀ x > 3, True.
Abort.

Goal ∀ x ≥ 3, True.
Abort.

Local Parameter B : subset nat.

Open Scope subset_scope.

Goal ∀ x ∈ B, x = 0.
Abort.

Goal ∃ x ∈ B, x = 0.
Abort.

Require Import Coq.Reals.Reals.
Close Scope nat_scope.
Open Scope R_scope.

Goal ∀ x > 3, x = 5.
Abort.

Goal ∃ x > 5, x = 7.
Abort.
