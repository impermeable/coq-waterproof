(** * Initialize global automation variables.
Authors: 
    - Lulof Pirée (1363638)
    - Cosmin Manea (small additions)
    - Tudor Voice (small additions)
    - Adrian Vrămuleţ (small additions)
    - Jim Portegies (Large reduction of file)
Creation date: 14 June 2021

File that initializes global variables for the 
waterprove automation.

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

(** * Global variable that collects a list of database labels
    (of type [WaterproofDatabase]).
    The databases corresponding to these labels will be used
    by the automation function [run_automation] in [waterprove.automation_subroutines],
    which is used in many different tactics.    
*)
Ltac2 mutable global_database_selection := fun () => ([]:ident list).
Ltac2 mutable global_negation_database_selection := fun () => ([]:ident list).
Ltac2 mutable global_decidability_database_selection := fun () => ([]:ident list).
Ltac2 mutable global_first_attempt_database_selection := fun () => ([]:ident list).

(** * global_search_depth
    Global variable that specifies the maximum search depth
    used by the automation tactics (via [run_automation] in [waterprove.automation_subroutines]).
*)
Ltac2 mutable global_search_depth := (2: int).

(** * global_debug_level
    Global variable that specifies the level of debug infos given by the automation tactics (via [run_automation] in [waterprove.automation_subroutines]).
*)
Ltac2 mutable global_debug_level := Std.Off.