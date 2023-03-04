(** * Enable the use of intuition in automation
Authors: 
    - Lulof Pirée (1363638)
Creation date: 21 June 2021

Set [global_enable_intuition] to [true].
This allows automated tactics to use [intuition] to solve a goal.
[auto] and [new_auto] will still be tried first.

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


Require Import Waterproof.message.
Require Import Waterproof.waterprove.automation_subroutine.

Ltac2 Set global_enable_intuition := true.