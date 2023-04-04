(** * Set search depth to 1
Authors: 
    - Lulof Pirée (1363638)
Creation date: 15 June 2021

Importing this file sets the maximum search depth to 1.
This limits the length of sequences of tactic combinations 
tried out used by automated tactics
(i.e. tactics that rely on [waterprove]).

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


Ltac2 Set global_search_depth := 1.