(** * [choose.v]
Author: 
    - Cosmin Manea (1298542)
Creation date: 20 May 2021

Two tactics for instantiating a variable according to a specific rule:
choose a specific value or when the hypothesis reads ``∃ n : N``, one can define such an `n`.
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
Require Import Waterproof.tactics.goal_wrappers.
Require Import Waterproof.definitions.set_definitions.
Require Import Waterproof.auxiliary.
Require Import Waterproof.tactics.forward_reasoning.forward_reasoning_aux.


Ltac2 Type exn ::= [ ChooseError(string) ].

Local Ltac2 raise_choose_error (s:string) := 
    Control.zero (ChooseError s).



(** * choose_varible_in_exists_goal_with_renaming
    Instantiate a variable in an [exists] [goal], according to a given [constr], and also renames
    the [constr].

    Arguments:
        - [s: ident], an [ident] for naming an idefined [constr]/variable.
        - [t: constr], the requirted [constr] that needs to be instantiated.

    Does:
        - instantiates the [constr] [t] under the name [s].

    Raises Exceptions:
        - [ChooseError], if the [goal] is not an [exists] [goal].
*)
Ltac2 choose_variable_in_exists_goal_with_renaming (s:ident) (t:constr) :=
    lazy_match! goal with
        | [ |- exists _ : subsets_R_to_elements ?sbst, _] =>
            if Aux.check_constr_type_equal t constr:(0%R) then
                let pred := constr:(is_in $sbst) in
                let dummy_hyp := Fresh.fresh (Fresh.Free.of_goal ()) @pf_el_in_set in 
                    Aux.ltac2_assert (dummy_hyp) constr:($pred $t);
                    let result := fun () => (
                    Control.focus 1 1 ( fun () => 
                        unfold is_in; simpl;
                        waterprove_without_hint constr:($pred $t) constr:(dummy_lemma) );
                    let my_witness := Control.hyp dummy_hyp in
                    pose ($s := mk_element_R $pred $t $my_witness);
                    let my_ident := Control.hyp s in
                    exists $my_ident) in
                match Control.case result with
                | Val _  => () 
                | Err exn => raise_choose_error ("First show that your element really is in the set")
                end
            else
                let v := s in pose ($v := $t); let id := Control.hyp s in exists $id
        | [ |- exists _ : _, _ ] => pose ($s := $t); let id := Control.hyp s in exists $id
        | [ |- _ ] => raise_choose_error("'Choose' can only be applied to 'exists' goals")
    end.



(** * choose_variable_in_exists_no_renaming
    Instantiate a variable in an [exists] [goal], according to a given [constr], without renaming
    said [constr].

    Arguments:
        - [t: constr], the requirted [constr] that needs to be instantiated.

    Does:
        - instantiates the [constr] [t] under the same name.

    Raises Exceptions:
        - [ChooseError], if the [goal] is not an [exists] [goal].
*)
Ltac2 choose_variable_in_exists_no_renaming (t:constr) :=
    lazy_match! goal with
        | [ |- exists _ : _, _] => exists $t
        | [ |- _ ] => raise_choose_error("'Choose' can only be applied to 'exists' goals")
    end.


Ltac2 Notation "Choose" t(constr) :=
    panic_if_goal_wrapped ();
    choose_variable_in_exists_no_renaming t.

Ltac2 Notation "Choose" s(ident) ":=" t(constr) :=
    panic_if_goal_wrapped ();
    choose_variable_in_exists_goal_with_renaming s t.