(** * we_show_both_statements.v
Authors: 
    - Cosmin Manea (1298542)
Creation date: 22 May 2021

Version of [We show/prove both statements] tactic.
[We show/prove both statements] can be used to split the proof of a conjunction.

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


From Waterproof Require Import auxiliary.


Ltac2 Type exn ::= [ BothStatementsError(string) ].

Ltac2 raise_both_statements_error (s:string) := 
    Control.zero (BothStatementsError s).


(** * both_directions_and
    Split the proof of a conjuction statement into both of its parts.

    Arguments:
        - no arguments

    Does:
        - splits the conjunction statement into its both parts.

    Raises Exceptions:
        - [BothStatementsError], if the [goal] is not a conjunction of statments.
*)
Ltac2 both_directions_and () :=
    lazy_match! goal with 
        | [ |- _ /\ _] => split
        | [ |- _ ] => raise_both_statements_error("This is not an 'and' statement, so try another tactic.")
    end.

Ltac2 Notation "We" show(opt("show")) prove(opt("prove")) "both" "statements" := 
    both_directions_and ().



(** * both_directions_specifically_stated
    Split the proof of a conjuction statement into two specified parts, but also verifies that the parts wrote
    by the user, in which the goal should split into, are the correct ones.

    Arguments:
        - [s: constr], the first part given.
        - [t: constr], the second part given.

    Does:
        - splits the [goal] into [s /\ t] or [t /\ s], if the goal can be written as such a conjuction.
        If it cannot be written, it prints a statement saying what the respective part that does not match
        should actually be.

    Raises Exceptions:
        - [BothStatementsError], if the [goal] is not a conjunction of the specified statments.
*)
Ltac2 both_directions_specifically_stated (s: constr) (t:constr) :=
    lazy_match! goal with
        | [ |- ?u /\ ?v] => match (Aux.check_constr_equal s u) with
                                | true => match (Aux.check_constr_equal t v) with
                                              | true => split
                                              | false => print( (Message.concat 
                                                                                (Message.concat (Message.of_string "You need to show ") 
                                                                                                (Message.of_constr v))
                                                                                (Message.concat (Message.of_string " instead of ")
                                                                                                (Message.of_constr t))
                                                                 ) 
                                                              )
                                          end
                                | false => match (Aux.check_constr_equal s v) with 
                                              | true => match (Aux.check_constr_equal t u) with 
                                                            | true => split
                                                            | false => print( (Message.concat 
                                                                                (Message.concat (Message.of_string "You need to show ") 
                                                                                                (Message.of_constr u))
                                                                                (Message.concat (Message.of_string " instead of ")
                                                                                                (Message.of_constr t))
                                                                              )
                                                                           )
                                                        end
                                              | false => match (Aux.check_constr_equal t u) with 
                                                            | true => print( (Message.concat 
                                                                                (Message.concat (Message.of_string "You need to show ") 
                                                                                                (Message.of_constr v))
                                                                                (Message.concat (Message.of_string " instead of ")
                                                                                                (Message.of_constr s))
                                                                             )
                                                                           )
                                                            | false => match (Aux.check_constr_equal t v) with 
                                                                           | true => print( (Message.concat
                                                                                                            (Message.concat (Message.of_string "You need to show ") 
                                                                                                            (Message.of_constr u))
                                                                                            (Message.concat (Message.of_string " instead of ")
                                                                                                            (Message.of_constr s))
                                                                                            )
                                                                                          )
                                                                           | false => raise_both_statements_error("None of these two statements are what you need to show.")
                                                                       end
                                                        end
                                           end
                            end
        | [ |- _ ] => raise_both_statements_error("This is not an 'and' statement, so try another tactic.")
    end.


Ltac2 Notation "We" "must" "show" "both" s(constr) "and" t(constr) :=
    both_directions_specifically_stated s t.
