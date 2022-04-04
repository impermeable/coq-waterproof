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

Local Ltac2 expected_of_type_instead_of_message (e : constr) (t : constr) := 
  Message.concat (Message.concat 
    (Message.concat (of_string "Expected variable of type ") (of_constr e))
    (Message.concat (of_string " instead of ") (of_constr t))) (of_string ".").


(** * intro_ident
    Introduces a variable.

    Arguments:
        - [id : ident ]: variable to introduce.
        - [type: constr]: type of the variable [id].
    Does:
        - Introduces the variable [id].
    Raises Exceptions:
        - [TakeError], if the current goal does not require the introduction
          of a variable of type [type], including coercions of [type].
*)
Local Ltac2 intro_ident (id : ident) (type : constr) :=
  lazy_match! goal with
  | [ |- forall _ : ?u, _] =>
         let ct := Aux.get_coerced_type type in
         (* Check whether we need a variable of type [type], including coercions of [type]. *)
         match Aux.check_constr_equal u ct with
         | true  => intro $id
         | false => Control.zero (TakeError (too_many_of_type_message type))
         end
  | [ |- _] => Control.zero (TakeError (too_many_of_type_message type))
  end.


(** * intro_per_type
    Introduces a list of variables of single type.

    Arguments:
        - [pair : (ident list * constr)]: list of variables paired with their type.
    Does:
        - Introduces the variables in [pair].
    Raises Exceptions:
        - [TakeError], if the current goal does not require the introduction
          of a variable of type [type], including coercions of [type].
*)
Local Ltac2 intro_per_type (pair : ident list * constr) :=
  match pair with
  | (ids, type) => 
      lazy_match! goal with
      | [ |- forall _ : ?u, _] => 
            (* Check whether [u] is not a proposition. *)
            let sort_u := Aux.get_value_of_hyp u in
            match Aux.check_constr_equal sort_u constr:(Prop) with
            | false =>
                 (* Check whether we need variables of type [type], including coercions of [type]. *)
                 let ct := Aux.get_coerced_type type in
                 match Aux.check_constr_equal u ct with
                 | true  => List.iter (fun id => intro_ident id type) ids
                 | false => Control.zero (TakeError (expected_of_type_instead_of_message u type))
                 end
            | true  => Control.zero (TakeError (of_string "‘Take ...’ cannot be used to prove an implication (⇨). Use ‘Assume that ...’ instead."))
            end
       | [ |- _ ] => Control.zero (TakeError (of_string "Tried to introduce too many variables."))
       end
  end.


(** * take
    Checks whether variables need to be introduced,
    attempts to introduce a list of variables of certain types.
*)
Local Ltac2 take (x : (ident list * constr) list) := 
  lazy_match! goal with
    | [ |- forall _ , _ ] => List.iter intro_per_type x
    | [ |- _ ] => Control.zero (TakeError (of_string "‘Take ...’ can only be used to prove a ‘for all’-statement (∀) or to construct a map (→)."))
  end.

Ltac2 Notation "Take" x(list1(seq(list1(ident, ","), ":", constr), "and")) := 
    panic_if_goal_wrapped ();
    take x.