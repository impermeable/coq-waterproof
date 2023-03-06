(** * [auxiliary.v]
Authors:
    - Jim Portegies
Creation date: 4 March 2023

A wrapper around the Ltac2 message capabilities so that 
a global verbosity variable can control the printing.

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
From Ltac2 Require Import Int.

(** * A mutable function that controls the verbosity. *)
Ltac2 mutable verbosity () := 0.

(** * print

     Only prints if the global verbosity is
     larger than or equal to zero.

     Arguments:
          - [msg : message] The message to print
*)
Ltac2 print (msg : message) :=
if (ge (verbosity ()) 0) then
     Message.print msg
     else ().

Ltac2 of_string := Message.of_string.

Ltac2 of_exn := Message.of_exn.

Ltac2 concat := Message.concat.

Ltac2 of_constr := Message.of_constr.

Ltac2 of_ident := Message.of_ident.

Ltac2 of_int := Message.of_int.
