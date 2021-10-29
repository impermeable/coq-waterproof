(** * [rewrite_using.v]
Authors: 
    - Cosmin Manea (1298542)
    - Lulof Pirée (1363638)
Creation date: 06 June 2021

Various versions of [Rewrite using ...] tactic. 
This tactic is used to rewrite the goal or hypotheses.
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
Require Import Waterproof.tactics.forward_reasoning.forward_reasoning_aux.
Require Import Waterproof.tactics.goal_wrappers.

Ltac2 Type exn ::= [ RewriteError(string) ].

Local Ltac2 fail_goal_rewrite () := 
        Control.zero (RewriteError 
            "Could not rewrite goal with this expression").

Ltac2 fail_verify_prop () :=
    Control.zero (AutomationFailure 
        "Could not verify that the proposition used for the rewrite holds.
You may need to prove this proposition first before rewriting others with it.").

Local Ltac2 print_rewrote_goal_success (proposition: constr) :=
    let prop := Aux.get_value_of_hyp proposition in
    print(concat 
        (concat
            (of_string "Successfully rewrote goal using '")
            (of_constr prop)
        )
        (of_string "'.")
    ).

(** * rewrite_attempt
    Try to rewrite the goal using [prop].
    Throw a custom error in case of failure,
    print a success message otherwise.

    Arguments:
        - [lemma:constr], the lemma (or theorem) used for the rewrite.
            This should be an equality proposition.
        - [target: ident option], optional name of hypothesis to rewrite.
            In case [None] is given, the goal will be rewritten.
        - [to_left: bool], direction in which the lemma should be used.
            - [true], the RHS of [lemma] will be interpreted as the current
                goal/hypothesis, and the goal will be rewritten toward the
                LHS. Equivalent to [rewrite <- ...].
            - [false], vice-versa, so using the normal [rewrite] without [<-].

    Raises exceptions:
        - [RewriteError], in case the goal/hypothesis could not be
            rewritten by [lemma] in the indicated direction.
*)
Local Ltac2 rewrite_attempt (lemma: constr)
                            (target : ident option)
                            (to_left: bool):=
    let f () :=
        match target with
        | None => 
            match to_left with
            | true => (rewrite <- $lemma)
            | false => (rewrite $lemma)
            end
        | Some id => 
            match to_left with
            | true => (rewrite <- $lemma in $id)
            | false => (rewrite $lemma in $id)
            end
        end
    in
    match Control.case f with
    | Val _ => () (* print_rewrote_goal_success lemma *)
    | Err exn => fail_goal_rewrite ()
    end.

(** * rewrite_with_prop_check 
    Try to rewrite a goal or hypothesis using a
    proposition litteral.
    First tries to prove the proposition,
    and then to rewrite the target with it.
    Raises an error in case either of the two steps fails.

    Arguments:
        - [proposition: constr], litteral proposition
            of the form ∀[... : ... = ...].
        - [target: ident option], optional name of hypothesis to rewrite.
            In case [None] is given, the goal will be rewritten.
        - [to_left: bool], direction in which the lemma should be used.
            - [true], the RHS of [lemma] will be interpreted as the current
                goal/hypothesis, and the goal will be rewritten toward the
                LHS. Equivalent to [rewrite <- ...].
            - [false], vice-versa, so using the normal [rewrite] without [<-].

    Raises exceptions:
        - [AutomationFailure], in case [proposition] could not be proven
            automatically. In this case, it may either be untrue,
            or too difficult to prove automatically.
        - [RewriteError], in case the goal/hypothesis could not be
            rewritten by [proposition] in the indicated direction.
*)
Ltac2 rewrite_with_prop_check (proposition: constr) 
                            (target : ident option)
                            (to_left: bool):=
    (* Add proposition as a new hypothesis, 
        then do the rewrite,
        and then remove this hypothesis again.*)
    let u := Fresh.in_goal @u in
    let by_arg () := waterprove_without_hint proposition constr:(dummy_lemma) false
    in
    let verify_prop () := Aux.ltac2_assert_with_by u proposition by_arg
    in
    match Control.case verify_prop with
    | Val _ =>
        rewrite_attempt (Control.hyp u) target to_left; clear u
    | Err exn => clear u; fail_verify_prop ()
    end.


(** * Rewrite using ...
    Try to rewrite the goal using [prop].
    Throw a custom error in case of failure,
    print a success message otherwise.
    Matches the LHS of [prop] to the goal,
    and tries to change part of expression towards the RHS.

    Arguments:
        - [prop:constr], the prop (or theorem) used for the rewrite.
            This should be an equality proposition. 

    Raises exceptions:
        - [RewriteError], in case the goal/hypothesis could not be
            rewritten by [prop] in the right-to-left direction.
*)
Ltac2 Notation "Rewrite" "using" prop(constr) :=
    panic_if_goal_wrapped ();
    rewrite_with_prop_check prop None false.

(** * Rewrite using ... in ...
    Try to rewrite a hypothesis using [prop].
    Throw a custom error in case of failure,
    print a success message otherwise.
    Matches the LHS of [prop] to the goal,
    and tries to change part of expression towards the RHS.

    Arguments:
        - [prop:constr], the prop (or theorem) used for the rewrite.
            This should be an equality proposition. 
        - [target: ident], name of hypothesis to rewrite.

    Raises exceptions:
        - [RewriteError], in case the goal/hypothesis could not be
            rewritten by [prop] in the right-to-left direction.
*)
Ltac2 Notation "Rewrite" "using" prop(constr) "in" target(ident):=
    panic_if_goal_wrapped ();
    rewrite_with_prop_check prop (Some target) false.

(** * Rewrite <- using ...
    Try to rewrite the goal using [prop].
    Throw a custom error in case of failure,
    print a success message otherwise.
    Matches the RHS of [prop] to the goal,
    and tries to change part of expression towards the LHS.

    Arguments:
        - [prop:constr], the prop (or theorem) used for the rewrite.
            This should be an equality proposition. 

    Raises exceptions:
        - [RewriteError], in case the goal/hypothesis could not be
            rewritten by [prop] in the left-to-right direction.
*)
Ltac2 Notation "Rewrite" "<-" "using" prop(constr) :=
    panic_if_goal_wrapped ();
    rewrite_with_prop_check prop None true.

(** * Rewrite <- using ... in ...
    Try to rewrite a hypothesis using [prop].
    Throw a custom error in case of failure,
    print a success message otherwise.
    Matches the RHS of [prop] to the goal,
    and tries to change part of expression towards the LHS.

    Arguments:
        - [prop:constr], the prop (or theorem) used for the rewrite.
            This should be an equality proposition. 
        - [target: ident], name of hypothesis to rewrite.

    Raises exceptions:
        - [RewriteError], in case the goal/hypothesis could not be
            rewritten by [prop] in the left-to-right direction.
*)
Ltac2 Notation "Rewrite" "<-" "using" prop(constr) "in" target(ident):=
    panic_if_goal_wrapped ();
    rewrite_with_prop_check prop (Some target) true.