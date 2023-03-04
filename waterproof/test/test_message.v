(** * Testcases for [inequality_chains.v]
Authors: 
    - Jim Portegies
Creation date: 4 Mar 2023

Testcases for messages.v
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

(* Tests for messages.v *)

From Ltac2 Require Import Ltac2.
Require Import Waterproof.test_auxiliary.

Load message.

(** Uncomment the next line to increase the test verbosity. *)
(* Ltac2 Set test_verbosity := fun () => 1. *)

Ltac2 store_verbosity := verbosity.

(** set below to true to actually do the tests. *)
Ltac2 verbose := fun () => if (ge (test_verbosity ()) 1) then true else false.

Ltac2 Set verbosity := fun () => if (verbose ())
    then 2 else -1.

(** Should print something if test_verbosity is larger than or equal to 1. *)
Goal True.
print (of_string "This string should be printed if test_verbosity is larger than or equal to 1.").
Abort.

Goal True.
Ltac2 Set verbosity := fun () => -1.
print (of_string "This should not be printed").
Abort.

(** Uncomment the following line to set the verbosity higher
    and print more messages. *)

Ltac2 Set verbosity := fun () => 1.

(** Should print a message: *)



Ltac2 Set verbosity := store_verbosity.
