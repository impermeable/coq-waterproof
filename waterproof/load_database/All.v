(** * [All.v]
Authors: 
    - Lulof Pirée (1363638)
    - Cosmin Manea (1298542)
    - Tudor Voicu (1339532)
    - Adrian Vrămuleţ (1284487)
Creation date: 15 June 2021

Importing this file adds all Waterproof hint databases 
to the set of databases used by automated tactics
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
Require Import Waterproof.selected_databases.


Require Export Waterproof.load_database.Multiplication.
Require Export Waterproof.load_database.ZeroOne.
Require Export Waterproof.load_database.AbsoluteValue.
Require Export Waterproof.load_database.Exponential.
Require Export Waterproof.load_database.PlusMinus.
Require Export Waterproof.load_database.SquareRoot.
Require Export Waterproof.load_database.RealsAndIntegers.
Require Export Waterproof.load_database.Sets.
Require Export Waterproof.load_database.Additional.
Require Export Waterproof.load_database.Subsets.
Require Export Waterproof.load_database.ClassicalLogic.