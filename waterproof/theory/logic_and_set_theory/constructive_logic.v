(** * Constructive logic

Authors:
    - Jim Portegies
    - Jelle Wemmenhove

Creation date: 25 Mar 2023.

This file derives additional lemmas about constructive logic.

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

(** TODO: fix this import. *)
Require Import Classical_Pred_Type.

Global Hint Resolve not_ex_all_not : constructive_logic.
Global Hint Resolve ex_not_not_all : constructive_logic.
Global Hint Resolve all_not_not_ex : constructive_logic.