(** * Testcases for the 'reals' database
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

(* Tests for (in)equality chains and the reals database *)


Load databases.

Open Scope R_scope.
(* Test 0: check if notations work. *)

Goal (& 3 < 4 <= 5).
auto with reals.
Qed.

Goal (& 3 = 3 = 3).
auto with reals.
Qed.
Open Scope R_scope.
(* Test 1: check if terms of a subset can be coerced to terms of the underlying set (here: [R]). *)
Goal forall x : R, (& x < 5 = 2 + 3) -> (x < 5).
intro x.
intro H.
auto with reals.
Qed.