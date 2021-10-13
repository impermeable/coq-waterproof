(** * [because.v]
Authors: 
    - Cosmin Manea (1298542)
    - Jelle Wemmenhove

Creation date: 23 May 2021
Latest edit:   12 oct 2021

Version of the [Because ... both/either ...] tactic.
This tactic uses an already existing result to prove that more results hold.
It is a form of forward reasoning.

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
Require Import Waterproof.auxiliary.
Require Export Waterproof.tactics.goal_wrappers.


(** * and_hypothesis_destruct
    Destruct an AND hypothesis into its respective two parts.

    Arguments:
        - [s: ident], the [ident] of the AND hypothesis.
        - [u: ident], the name of the first part of [s].
        - [v: ident], the name of the second part of [s].

    Does:
        - splits [s] into its two respective parts.
*)
Local Ltac2 and_hypothesis_destruct (s:ident) (u:ident) (v:ident) :=
    let s_val := Control.hyp s in (destruct $s_val as [$u $v]).





Ltac2 Notation "Because" s(ident) "both" u(ident) "and" v(ident) :=
    panic_if_goal_wrapped ();
    and_hypothesis_destruct s u v.

Ltac2 Notation "Because" s(ident) "both" u(ident) ":" tu(constr) "and" v(ident) ":" tv(constr) 
:=  panic_if_goal_wrapped ();
    and_hypothesis_destruct s u v.

