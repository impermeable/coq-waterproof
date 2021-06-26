(** * [apply.v]
Authors: 
    - Cosmin Manea (1298542)

Creation date: 06 June 2021

Version of [Apply] tactic. This allows the user to apply a lemma to prove the current goal.
--------------------------------------------------------------------------------

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

From Ltac2 Require Import Ltac2.

(** * apply_lemma
    Applies a lemma to prove the current goal.

    Arguments:
        - [lemma: constr], the lemma to be applied.

    Does:
        - applies [lemma] in proving the current [goal].
*)
Local Ltac2 apply_lemma (lemma: constr) :=
    apply $lemma.



Ltac2 Notation "Apply" t(constr) :=
    apply_lemma t.