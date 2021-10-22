(** * [it_holds_that.v]
Authors: 
    - Lulof Pirée (1363638)
Creation date: 6 June 2021

Tactic [It holds that ...].
Used to prove intermediate statements.

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

Require Import Waterproof.tactics.forward_reasoning.forward_reasoning_aux.
Require Import Waterproof.auxiliary.
Require Import Waterproof.waterprove.waterprove.
Require Import Waterproof.tactics.goal_wrappers.

(** * By ... it holds that ... : ...
    Introduce a new sublemma and try to prove it immediately,
    optionally using a given lemma.

    Arguments:
        - [id: ident], name for the new sublemma.
            If the proof succeeds, 
            it will become a hypotheses bearing [id] as name.
        - [conclusion: constr], the actual content 
            of the new sublemma to prove.
        - [proving_lemma: constr], optional reference to a lemma 
            used to prove the new sublemma (via [waterprove)]).

    Raises exception:
        - [AutomationFailure], if [waterprove] fails the prove the sublemma.
            This happens if the sublemma does not hold,
            but can also happen if it is simply too difficult for [waterprove].
*)
Ltac2 assert_and_prove_sublemma (id: ident) (conclusion: constr) 
                                (proving_lemma: constr option) :=
    let help_lemma := unwrap_optional_lemma proving_lemma
    in
    let by_arg () := waterprove_without_hint conclusion help_lemma
    in
    let proof_attempt () := Aux.ltac2_assert_with_by id conclusion by_arg
    in
    match Control.case proof_attempt with
    | Val _ => print (of_string ("New sublemma successfully added."))
    | Err exn => Control.zero exn
    end.

(** * By ... it holds that ... : ...
    Introduce a new sublemma and try to prove it immediately
    using a given lemma.

    Arguments:
        - [lemma: constr], reference to a lemma 
            used to prove the new sublemma (via [waterprove)]).
        - [id: ident], name for the new sublemma.
            If the proof succeeds, 
            it will become a hypotheses bearing [id] as name.
        - [conclusion: constr], the actual content 
            of the new sublemma to prove.

    Raises exception:
        - [AutomationFailure], if [waterprove] fails the prove the sublemma.
            This happens if the sublemma does not hold,
            but can also happen if it is simply too difficult for [waterprove].
*)
Ltac2 Notation "By" lemma(constr) 
               "it" "holds" "that" id(ident) ":" conclusion(constr) := 
    panic_if_goal_wrapped ();
    assert_and_prove_sublemma id conclusion (Some lemma).
    
    
(** * It holds that ... : ...
    Introduce a new sublemma and try to prove it immediately.
    Same as [By ... it holds that ... : ...],
    but without using a specified lemma.

    Arguments:
        - [id: ident], name for the new sublemma.
            If the proof succeeds, 
            it will become a hypotheses bearing [id] as name.
        - [conclusion: constr], the actual content 
            of the new sublemma to prove.

    Raises exception:
        - [AutomationFailure], if [waterprove] fails the prove the sublemma.
            This happens if the sublemma does not hold,
            but can also happen if it is simply too difficult for [waterprove].
*)
Ltac2 Notation "It" "holds" "that" id(ident) ":" conclusion(constr) :=
    panic_if_goal_wrapped ();
    assert_and_prove_sublemma id conclusion None.