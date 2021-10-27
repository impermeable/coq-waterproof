(** * [take.v]
Authors: 
    - Lulof Pirée (1363638)
    - Cosmin Manea (1298542)
    - Jelle Wemmenhove
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


Local Ltac2 too_many_of_type_message (t : constr) := 
  Message.concat (Message.concat (of_string "Tried to introduce too many variables of type ") (of_constr t)) (of_string ".").

(** * introduce_idents
    Attempts to recursively introduce variables of one type.

    Arguments:
        - [x : ident list]: list of variables to introduce. 
        - [t: constr]: type of the variables in [x].
        - [ct : constr]: coercion of type [t].
    Does:
        - If possible, introduces the first variable in [x]. 
          Proceeds to call itself with the remaining variables in [x] as a new list [x'].

    Raises Exceptions:
        - [TakeError], if the current goal does not require the introduction of any more variables 
                       in general or of type [t].
*)
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


Local Ltac2 expected_of_type_instead_of_message (e : constr) (t : constr) := 
  Message.concat (Message.concat 
    (Message.concat (of_string "Expected variables of type ") (of_constr e))
    (Message.concat (of_string " instead of ") (of_constr t))) (of_string ".").

(** * process_identlist_type_pairs
    Attempts to recursively introduce a list of (variables of a specific type).

    Arguments:
        - [x : (ident list * constr) list)]: list of (variables paired with a specific type).
    Does:
        - For the first pair of (variables coupled with a type) in [x], 
            calls [introduce_idents] to introduce these variables.
          Proceeds to call itself with the remaining pairs in [x] as a new list [x'].

    Raises Exceptions:
        - [TakeError], if the current goal does not require the introduction of any more variables 
                       in general or of type [t], where [t] is the type from the first pair in [x].
*)
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

(** * take
    Checks whether the 'Take' tactic can be applied to the current goal, 
    attempts to introduce a list of (variables of a specific type).
*)
Local Ltac2 take (x : (ident list * constr) list) := 
  lazy_match! goal with
    | [ |- forall _ , _ ] => process_identlist_type_pairs x
    | [ |- _ ] => Control.zero (TakeError (of_string "‘Take’ can only be used to prove a ‘for all’-statement (∀) or to construct a map (→)."))
  end.

Ltac2 Notation "Take" x(list1(seq(list1(ident, ","), ":", constr), "and")) := 
    panic_if_goal_wrapped ();
    take x.