(** * Testcases for [inequality_chains.v]
Authors: 
    - Jim Portegies
Creation date: 30 Oct 2021

Testcases for (in)equality chains.
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

(* Tests for (in)equality chains *)

Load inequality_chains.

(* Test 0: check if notations work. *)

Goal (& 3 &< 4 &<= 5).
Abort.

(* Test 1: check if terms of a subset can be coerced to terms of the underlying set (here: [R]). *)
Goal (3 < 5) /\ (5 = 2 + 3) <-> (& 3 &< 5 &= 2 + 3).
split.
- intro H.
  unfold ineq_to_prop.
  simpl.
  unfold R_as_OT.lt.
  unfold R_as_OT.eq.
  destruct H.
  repeat split.
  + assumption.
  + assumption.

- intro H.
  unfold ineq_to_prop in H.
  simpl in H.
  destruct H.
  destruct H0.

  unfold R_as_OT.lt in H.
  unfold R_as_OT.eq in H0.
  split.
  + assumption.
  + assumption.
Qed.