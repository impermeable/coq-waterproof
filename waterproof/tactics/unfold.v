(** * unfold.v
Authors: 
    - Cosmin Manea (1298542)
    - Lulof Pirée (1363638)

Creation date: 06 June 2021

Custom notation for the build-in [unfold] tactic.

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
From Ltac2 Require Import Option.

Require Import Waterproof.auxiliary.

(** * Unfold
    Rewrite a function by its definition,
    in the goal or in a hypothesis.
    Nothing more than a custom notation for the build-in [unfold].

    Exactly same implementation as in Ltac2's source file [Notations.v].
    The only difference is that the [U] is capitalized.
    Note that the [opt(clause)] syntactic class handles the optional
    keyword [in].

    Arguments:
        - [targets: constr] or [targets: constr list],
            the target function to unfold, 
            or the target functions (separated by [,]) to unfold.
        - [in_clause: constr], optional suffix with syntax 
            [unfold f in h] for some [h],
            where [h] is the hypothesis to rewrite the function [f] in.
            If omitted, [f] is rewritten in the goal.

*)
Ltac2 Notation "Unfold" targets(list1(seq(reference, occurrences), ",")) 
                        in_clause(opt(clause)) :=
    Std.unfold targets (Notations.default_on_concl in_clause).

(* Same as above, but different notation. *)
Ltac2 Notation "Expand" "the" "definition" "of" targets(list1(seq(reference, occurrences), ",")) 
    in_clause(opt(clause)) :=
Std.unfold targets (Notations.default_on_concl in_clause).