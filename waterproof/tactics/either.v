(** * [either.v]
Authors: 
    - Cosmin Manea (1298542)
    - Jelle Wemmenhove

Creation date: 02 June 2021
Latest edit:   13 Oct 2021

Tactic for proving by case distinction.
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
(* Database for 'Either ... or ...' tactic. *)
Require Import Waterproof.tactics.automation_databases.decidability_db.
Require Import Waterproof.auxiliary.
Require Export Waterproof.tactics.goal_wrappers.

Ltac2 Type exn ::= [ CaseError(string) | InputError(message) ].

(** *
    Removes the Case.Wrapper.

    Arguments:
        - [t : constr], case in which the goal is wrapped

    Does:
        - removes the Case.Wrapper from the goal

    Raises Exceptions:
        - [CaseError], if the [goal] is not wrapped in the case [t], i.e. the goal is not of 
                       the form [Case.Wrapper t G] for some type [G].
*)
Ltac2 case (t:constr) := lazy_match! goal with
                         | [|- Case.Wrapper ?v _] => 
                          match Constr.equal v t with
                          | true => apply (Case.wrap $v)
                          | false => Control.zero (CaseError "Wrong case specified.")
                          end
                         | [|- _] => Control.zero (CaseError "No need to specify case.")
                         end.
Ltac2 Notation "Case" t(constr) := case t.



(** * either_case_1_or_case_2
    Split the proof by case distinction.

    Arguments:
        - [t1 : constr], the first case.
        - [t2 : constr], the second case.

    Does:
        - splits the proof by case distinction; wraps the resulting goals in the Case.Wrapper
*)
Ltac2 either_or (t1:constr) (t2:constr) 
:= (assert ({$t1} + {$t2}) as u by auto with decidability nocore);
   destruct u; Control.focus 1 1 (fun () => apply (Case.unwrap $t1));
               Control.focus 2 2 (fun () => apply (Case.unwrap $t2)).
(* Removed the attempt 'assert t2 + t1' because this switches the ordering specified by the user. *)

Ltac2 Notation "Either" t1(constr) "or" t2(constr) := 
    panic_if_goal_wrapped ();
    either_or t1 t2.



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

Local Ltac2 type_of_should_be_msg (u:ident) (type_u:constr)
 := concat (concat (concat (of_string "Type of ") (of_ident u))
                   (concat (of_string " should be ") (of_constr type_u))) (of_string ".").

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

