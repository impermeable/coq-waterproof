(** * [because.v]
Authors: 
    - Cosmin Manea (1298542)
    - Jelle Wemmenhove

Creation date: 23 May 2021

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
From Ltac2 Require Import Message.
Require Import Waterproof.auxiliary.
Require Export Waterproof.tactics.goal_wrappers.
Require Export Waterproof.tactics.either. (* Enable the unwrapping of the Case wrapper. *)

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


Local Ltac2 idtac () := ().

Local Ltac2 type_of_should_be_msg (u:ident) (type_u:constr)
 := concat (concat (concat (of_string "Type of ") (of_ident u))
                   (concat (of_string " should be ") (of_constr type_u))) (of_string ".").

(** * and_hypothesis_destruct_with_types
    Destruct an AND hypothesis into its respective two parts if the 
    types of the respective parts are correctly specified.

    Arguments:
        - [s: ident], the [ident] of the AND hypothesis.
        - [u: ident], the name of the first part of [s].
        - [tu : constr], specified type of the first part of [s].
        - [v: ident], the name of the second part of [s].
        - [tv : constr], specified type of the second part of [s].

    Does:
        - splits [s] into its two respective parts.

    Raises Exceptions:
        - [InputError] if the specified type [tu] or [tv] is not actually the type of [u] or [v] resp.
*)
Local Ltac2 and_hypothesis_destruct_with_types (s:ident) (u:ident) (tu:constr) (v:ident) (tv:constr) :=
    let s_val := Control.hyp s in
    destruct $s_val as [$u $v];
    let type_u := Aux.get_value_of_hyp_id u in
    match Constr.equal type_u tu with
    | true  => idtac ()
    | false => Control.zero (InputError (type_of_should_be_msg u type_u))
    end;
    let type_v := Aux.get_value_of_hyp_id v in
    match Constr.equal type_v tv with
    | true => idtac ()
    | false => Control.zero (InputError (type_of_should_be_msg v type_v))
    end.

Ltac2 Notation "Because" s(ident) "both" u(ident) "and" v(ident) :=
    panic_if_goal_wrapped ();
    and_hypothesis_destruct s u v.

Ltac2 Notation "Because" s(ident) "both" u(ident) ":" tu(constr) "and" v(ident) ":" tv(constr) 
:=  panic_if_goal_wrapped ();
    and_hypothesis_destruct_with_types s u tu v tv.



(** * or_hypothesis_destruct
    Destruct an OR hypothesis into its respective two parts. Wraps the goal for both parts.

    Arguments:
        - [s: ident], the [ident] of the OR hypothesis.
        - [u: ident], the name of the first part of [s].
        - [v: ident], the name of the second part of [s].

    Does:
        - splits [s] into its two respective parts. Wraps the goal for both parts in the
          [Case.Wrapper] wrapper.
*)
Local Ltac2 or_hypothesis_destruct s u v :=
    let s_hyp := Control.hyp s in
    destruct $s_hyp as [$u | $v];
    Control.focus 1 1 (fun () => let type_u := Aux.get_value_of_hyp_id u in 
                                 apply (Case.unwrap $type_u));
    Control.focus 2 2 (fun () => let type_v := Aux.get_value_of_hyp_id v in
                                 apply (Case.unwrap $type_v)).

(** * or_hypothesis_destruct_with_types
    Destruct an OR hypothesis into its respective two parts if the 
    types of the respective parts are correctly specified. Wraps the goal for both parts.

    Arguments:
        - [s: ident], the [ident] of the OR hypothesis.
        - [u: ident], the name of the first part of [s].
        - [tu : constr], specified type of the first part of [s].
        - [v: ident], the name of the second part of [s].
        - [tv : constr], specified type of the second part of [s].

    Does:
        - splits [s] into its two respective parts. Wraps the goal for both parts in the
          [Case.Wrapper] wrapper.
    
    Raises Exceptions:
        - [InputError] if the specified type [tu] or [tv] is not actually the type of [u] or [v] resp.
*)
Local Ltac2 or_hypothesis_destruct_with_types (s:ident) (u:ident) (tu:constr) (v:ident) (tv: constr)
 := let s_hyp := Control.hyp s in
    destruct $s_hyp as [$u | $v];
    Control.focus 1 1 (fun () =>
      let type_u := Aux.get_value_of_hyp_id u in
      match Constr.equal type_u tu with
      | true => apply (Case.unwrap $type_u)
      | false => Control.zero (InputError (type_of_should_be_msg u type_u))
      end);
    Control.focus 2 2 (fun () =>
      let type_v := Aux.get_value_of_hyp_id v in
      match Constr.equal type_v tv with
      | true => apply (Case.unwrap $type_v)
      | false => Control.zero (InputError (type_of_should_be_msg v type_v))
      end).

Ltac2 Notation "Because" s(ident) "either" u(ident) "or" v(ident) :=
    panic_if_goal_wrapped ();
    or_hypothesis_destruct s u v.

Ltac2 Notation "Because" s(ident) "either" u(ident) ":" tu(constr) "or" v(ident) ":" tv(constr)
:=  panic_if_goal_wrapped ();
    or_hypothesis_destruct_with_types s u tu v tv.
