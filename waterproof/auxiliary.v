(** * [auxiliary.v]
Authors:
    - Lulof Pirée (1363638)
Creation date: 14 May 2021

Generic auxiliary functions.

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

Require Import Waterproof.message.

Module Aux.

(* Defensive programming error *)
Ltac2 Type exn ::= [ CannotHappenError(string) ].

Ltac2 cannot_happen (message: string) :=
    Control.throw (CannotHappenError message).

End Aux.