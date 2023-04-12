(** * Enables the debug [auto] printing
Authors: 
    - Balthazar Patiachvili
Creation date: 11 April 2023

Set [global_debug_level] to [Std.Debug] and Ltac2 Backtrace flage on.
This prevents [auto] to print info and/or debug message.

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

Require Import Waterproof.init_automation_global_variables.

Set Ltac2 Backtrace.
Ltac2 Set global_debug_level := Std.Debug.