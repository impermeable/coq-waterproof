(** * [take.v]
Authors: 
    - Lulof Pirée (1363638)
    - Cosmin Manea (1298542)
Creation date: 17 May 2021

Version of [Take] tactic that accepts any number of arguments.
[Take] can be used to eliminate a ∀ clause in the goal,
by introducing variables.

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
Require Import Waterproof.tactics.goal_wrappers.

Ltac2 Type exn ::= [ TakeError(message) ].

(** * intro_with_type_matching
    Check if the goal is a ∀-quantifier over a bound variable
    of type [t]. 
    In case it is, introduce such a variable with ident [s].
    If it is not, raise an error.

    Arguments:
        - [s:Std.intro_pattern list], name for variable to introduce.
            Despite being of type [list], this can simply be a single name
            as parsed by [Ltac2 Notation].
        - [t:constr], the type of the variable to introduce.

    Does:
        - perform ∀-elim by introducing s as a variable of type [t].
            (Call [intros $s])

    Raises Exceptions:
        - [TakeError], if the type [t] 
            does not match the type of the bound variable in the ∀-goal.
        - [TakeError], if the top-level connective in the goal 
            is not a ∀-quantifier.
*)

(** * intro_list_with_typematching
    Introduce for each name in the list [x] a new variable of type [t].

    Arguments:
        - [x]: a list of intropatterns
        - [t: constr], the type of the variables to introduce.
    Does:
        - call [intro_with_type_matching v t] for each [v] ∈ [x].

    Raises Exceptions:
        - [TakeError], if the top-level connective in the goal 
            is not a ∀-quantifier, or if the variables of [x]
            cannot all be introduced as of type [t].
*)

Local Ltac2 too_many_of_type_message (t : constr) := 
  Message.concat (Message.concat (of_string "Tried to introduce too many variables of type ") (of_constr t)) (of_string ".").

Local Ltac2 rec introduce_idents (x : ident list) (t : constr) (ct : constr) :=
  match x with
  | head::tail 
    => (* Check whether we still need variables of coerced type [ct]. *)
       lazy_match! goal with
       | [ |- forall _ : ?u, _] 
         => match Aux.check_constr_equal u ct with
            | true  => (* Introduce head *)
                       Std.intros false [Std.IntroNaming (Std.IntroIdentifier head)];
                       (* Attempt to introduce remaining variables. *)
                       introduce_idents tail t ct
            | false => Control.zero (TakeError (too_many_of_type_message t))
            end
       | [ |- _] => Control.zero (TakeError (of_string "Tried to introduce too many variables."))
       end
  | [] => () (*done*)
  end.

(** * take_multiarg

    Takes a list of [(name_list, type)] tuples, and introduces each
    name in each [name_list] as a new variable of type [type].

    Arguments:
        - x: a list of (v, t) pairs, where each [t: constr]
            and each [v : Std.intro_pattern list list].
    Does:
        - call [intro_list_with_typematching (v, t)] for each (v, t) ∈ x

    Raises Exceptions:
        - [TakeError], if the top-level connective in the goal 
            is not a ∀-quantifier, or if the variables of the given type
            cannot all be introduced (in the given order).

*)
Local Ltac2 expected_of_type_instead_of_message (e : constr) (t : constr) := 
  Message.concat (Message.concat 
    (Message.concat (of_string "Expected variables of type ") (of_constr e))
    (Message.concat (of_string " instead of ") (of_constr t))) (of_string ".").

Local Ltac2 rec process_identlist_type_pairs (x : (ident list * constr) list) :=
    match x with
    | head::tail =>
            match head with
            | (v, t) => (* Check whether we need variabled of type t. *)
                        lazy_match! goal with
                        | [ |- forall _ : ?u, _] => 
                            let ct := Aux.get_coerced_type t in
                            match Aux.check_constr_equal u ct with
                            | true  => introduce_idents v t ct
                            | false => Control.zero (TakeError (expected_of_type_instead_of_message u t))
                            end
                        | [ |- _ ] => Control.zero (TakeError (of_string "Tried to introduce too many variables."))
                        end
            | _ => Control.zero (Aux.CannotHappenError "Cannot happen.")
            end;
            (* Attempt to introduce remaining variables of (different) types. *)
            process_identlist_type_pairs tail
    | [] => () (* Done. *)
    end.

Local Ltac2 take (x : (ident list * constr) list) := 
  lazy_match! goal with
    | [ |- forall _ , _ ] => process_identlist_type_pairs x
    | [ |- _ ] => Control.zero (TakeError (of_string "‘Take’ can only be used to prove a ‘for all’-statement (∀) or to construct a map (→)."))
  end.

Ltac2 Notation "Take" x(list1(seq(list1(ident, ","), ":", constr), "and")) := 
    panic_if_goal_wrapped ();
    take x.