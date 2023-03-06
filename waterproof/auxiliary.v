(** * [auxiliary.v]
Authors:
    - Lulof Pirée (1363638)
Creation date: 14 May 2021

Generic auxiliary functions.

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

Require Import Waterproof.message.

Module Aux.

(* Defensive programming error *)
Ltac2 Type exn ::= [ CannotHappenError(string) ].

Ltac2 cannot_happen (message: string) :=
    Control.throw (CannotHappenError message).

(** * type_of
    Gallina function mapping a term of a type
    to the type itself.

    Arguments:
        - [T:type], any type
        - [x:T], a term of a generic type T.
    Returns:
        - [T], the type of x.
*)
Definition type_of {T : Type} (x : T) := T.

(** * get_value_of_hyp_id
    Given an [constr] that is the reference of a hypothesis
    (i.e. the LHS in the proof context,
    e.g. the [h] in [h: 1 + 1 = 2]),
    return the unnormalized value of the hypothesis.

    Arguments:
        - [hyp: constr], LHS of the hypothsis.

    Returns:
        - [constr]: unnormalized type of the hypothesis
            (i.e. the RHS).
*)
Ltac2 get_value_of_hyp (hyp: constr) :=
    eval unfold type_of in (type_of $hyp).

(** * get_value_of_hyp_id
    Given an [ident] matching a hypothesis,
    return the unnormalized value of the hypothesis.

    Arguments:
        - [hyp_id: ident], name of hypothesis.

    Returns:
        - [constr]: unnormalized type of the hypothesis.
*)
Ltac2 get_value_of_hyp_id (hyp_id: ident) :=
    let h := Control.hyp hyp_id in
    get_value_of_hyp h.



(** * check_constr_type_equal  
    Ltac2 function: [constr -> constr -> bool].
    Check if the normalized TYPE OF [a] is syntactically 
    equal to the normalized TYPE OF [b].

    Arguments:
        - [a, b: constr], any [constr]
    Returns:
        - [bool]:
            - [true] if the TYPES OF [a] and [b] are syntactically equal
                (i.e. are of the same type after normalization)
            - [false] otherwise.
*)  
Ltac2 check_constr_type_equal (a: constr) (b: constr) :=
    Constr.equal (eval cbv in (type_of $a)) (eval cbv in (type_of $b)).

(** * check_constr_equal
    Ltac2 function: [constr -> constr -> bool]
    Check if the normalized form of [a] is syntactically 
    equal to the normalized form of [b].

    Arguments:
        - [a, b: constr], any [constr]
    Returns:
        - [bool]:
            - [true] if a and b are syntactically equal
                (i.e. are of the same type after normalization)
            - [false] otherwise.
*)  
Ltac2 check_constr_equal (a: constr) (b: constr) :=
    Constr.equal (eval cbv in $a) (eval cbv in $b).


(** Subroutine of [print_all_hyps]*)
Local Ltac2 rec print_all_hyps_rec (x : (ident * constr option * constr) list) :=
    match x with
    | head::tail =>
        match head with
        | (name, dunno, type) => print
            (Message.concat 
                (Message.concat (Message.of_ident name) 
                                (of_string " : "))
                (Message.of_constr type)
            );
            print_all_hyps_rec tail
        | _ => Control.zero (CannotHappenError "Cannot happen")
        end
    | [] => ()
    end.

(** * print_all_hyps
    Print all hypotheses of the current context as [ident : type] pairs,
    each on a separate line.
*)
Ltac2 print_all_hyps () := print_all_hyps_rec (Control.hyps ()).


(** * print_bool
    Prints the value of an Ltac2 [bool] to the output.

    Arguments:
        - [b: bool], any Ltac2 [bool] term.
    
    Does:
        - print "true" if [b] is [true], print "false" otherwise.
*)
Ltac2 print_bool (b: bool) :=
    match b with
    | true => print (of_string "true")
    | false => print (of_string "false")
    end.

(** * ltac2_assert
    Introduce *and prove* a new sublemma.
    Wrapper for the build-in Gallina [assert] statement
    that can accept Ltac2 variables as arguments.
    Includes a 'by' clause as used in
    [assert (... : ...) by ...].

    Arguments:
        - [id: ident], name of the new sublemma to prove.
        - [lemma_content: constr], new proposition to prove.
        - [by_arg: unit -> unit], 
            function that tries the prove the new sublemma.
*)
Ltac2 ltac2_assert_with_by (id: ident) (lemma_constent: constr)
                           (by_arg: unit -> unit) :=
    (** [Std.assert] expects an [AssertType] as argument.
        An [AssrtType] consist of three parts:
        - an [intropatterns opt]. 
            The whole [(Some (Std.IntroNaming (Std.IntroIdentifier id)))] 
            thing just wraps an [ident] into an optional [intropatterns].
        - A [constr], the actual propositions to assert.
        - Optionally, the method to prove the proposition 
            (e.g. manually done with "by [something]"). 
            This is an optional [unit -> unit]. 
            It is a series of tactic executions used to prove the [constr].
    *)
    Std.assert (Std.AssertType 
        (Some (Std.IntroNaming (Std.IntroIdentifier id))) 
        lemma_constent (Some by_arg)).

(** * ltac2_assert
    Introduce a new sublemma.
    Wrapper for the build-in Gallina [assert] statement
    that can accept Ltac2 variables as arguments.

    Arguments:
        - [id: ident], name of the new sublemma to prove.
        - [lemma_content: constr], new proposition to prove.
*)
Ltac2 ltac2_assert (id: ident) (lemma_content: constr) :=
    Std.assert (Std.AssertType 
        (Some (Std.IntroNaming (Std.IntroIdentifier id))) 
        lemma_content None).

(** * Get coerced type on intro

    If t is a term, the following tactics allow to extract what t gets
    coerced to after an introduction in forall x : t, True.
    
    ** Auxiliary function to get a coerced type
    Returns:
        - [constr] The coercion of t if the goal is forall x : t, True.

*)
Ltac2 get_coerced_type_aux () :=
    match! goal with
    | [ |- ?c -> True ] =>  c
    end.

(** ** Get coerced type

    If t is a term, the following tactic allows to extract what t gets
    coerced to after an introduction in forall x : t, True.

    Arguments:
        - [t : constr] The term to be coerced

    Returns:
        - [constr] The coerced term after introduction in forall x : t, True.
*)
Ltac2 get_coerced_type (t : constr) :=
    let dummy_hyp := Fresh.fresh (Fresh.Free.of_goal ()) @dummy_hypothesis in 
    ltac2_assert (dummy_hyp) constr:(forall _ : $t, True);
    (* the previous line creates an extra goal, which causes multiple goals to 
    focus. Goal matching panics on this, so we need to refocus on the first goal *)
    let z := Control.focus 1 1 (get_coerced_type_aux) in
      Control.focus 1 1 (fun () => exact (fun x => I)); (* prove the lemma *)
      clear $dummy_hyp; (* clear the resulting hypothesis *)
      z.

Ltac2 Type exn ::= [ UnsupportedError(string) ].
(** * int_to_constr
    Map an Ltac2 [int] to a [constr].

    Arguments:
        - [x: int], an Ltac2 integer in range [0, 5].

    Returns:
        - [constr], Gallina constructor representing the same number.
    
    Raises exceptions:
        - [UnsupportedError], in case [x > 5] or [x < 0].
*)
Ltac2 int_to_constr (x: int) :=
    match Int.equal x 0 with
    | true => constr:(0)
    | false =>
    match Int.equal x 1 with
    | true => constr:(1)
    | false =>
    match Int.equal x 2 with
    | true => constr:(2)
    | false =>
    match Int.equal x 3 with
    | true => constr:(3)
    | false =>
    match Int.equal x 4 with
    | true => constr:(4)
    | false =>
    match Int.equal x 5 with
    | true => constr:(5)
    | false => Control.zero 
        (UnsupportedError "Can only convert up to 5.")
    end end end end end end.

End Aux.