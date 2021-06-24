(** * choose_such_that.v
Author: 
    - Cosmin Manea (1298542)
Creation date: 30 May 2021

Various tactics for instantiating a variable according to a specific rule given from a
previously known result.
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



(** * choose_destrct_without_extra_hypothesis
    Chooses a variable according to a particular definition, and label the remaining parts 
    of the definition.

    Arguments:
        - [s: ident], the variable to be chosen.
        - [v: constr], the definition used.
        - [u: ident], the remaining parts of the definition.

    Does:
        - destructs the constr [v] under the names [s] and [u].
*)
Ltac2 choose_destruct_without_extra_hypothesis (s:ident) (u:ident) (v:constr) :=
   destruct $v as [$s $u].



Ltac2 Notation "Choose" s(ident) "such" "that" u(ident) "according" "to" v(constr) :=
    choose_destruct_without_extra_hypothesis s u v.