(** * [we_know.v]
Authors: 
    - Lulof Pirée (1363638)
    - Cosmin Manea (refactored file)
Creation date: 17 June 2021

Tactic for reminding the reader/user of the currently known hypotheses.
This tactic simply checks if a hypothesis with the name [H] and with type [T] 
exists in the current context.
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

Require Import Waterproof.auxiliary.
Require Import Waterproof.test_auxiliary.



Ltac2 Type exn ::= [ WeKnowError(string) ].

Ltac2 raise_we_know_error (s:string) := 
    Control.zero (WeKnowError s).




(** * check_hypothesis
    Checks whether or not a hypothesis, in form of a [constr], is indeed known to be true in the
    current context.

    Arguments:
        - [s: ident], the name/identifier of the repsective hypothesis.
        - [t: constr], the previously mentioned hypothesis.

    Does:
        - checks whether or not the [constr] that has [s] as its identifier is equal
          to the [constr] [t].

    Raises Exceptions:
        - [WeKnowError], if the hypothesis [t] does not exist.
*)
Ltac2 check_hypothesis (s: ident) (t: constr) :=
    let h := (Control.hyp s) in
    match Constr.equal (eval cbv in (Aux.type_of $h)) (eval cbv in $t) with 
        | true => print (concat (of_string "We indeed know that ") 
                        (of_constr (eval cbn in $t)))
        | false => raise_we_know_error("This hypothesis does not exist.")
    end. 


Ltac2 Notation "We" "know" s(ident) ":" t(constr) := check_hypothesis s t.

Ltac2 Notation "By" s(ident) "we" "know" t(constr) := check_hypothesis s t.





