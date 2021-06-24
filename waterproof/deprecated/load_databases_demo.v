(** * [load_databases_demo.v]

Authors: 
    - Lulof Pirée (1363638)
Creation date: 18 June 2021

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
From Ltac2 Require Option.
From Ltac2 Require Import Message.

Require Import Waterproof.test_auxiliary.
Require Import Waterproof.selected_databases.
Require Import Waterproof.waterprove.waterprove.





Ltac2 Eval print (of_string "Initial database selection is:").
Ltac2 Eval global_database_selection. 

Require Import load_database.Multiplication.
Require Import load_database.PlusMinus.
Ltac2 Eval print (of_string "Current database selection is:").
Ltac2 Eval global_database_selection.






Ltac2 Eval print (of_string "Initial search depth is:").
Ltac2 Eval global_search_depth. 

Require Import Waterproof.set_search_depth.To_1.
Ltac2 Eval print (of_string "Current search depth is:").
Ltac2 Eval global_search_depth.