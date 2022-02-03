(** * [assume.v]
Authors: 
    - Lulof Pirée (1363638)
    - Jelle Wemmenhove
Creation date: 20 May 2021

[Assume] can be used to introduce the premise of an implication (⇒)
as an hypothesis.
It expectes a type annotation for each hypothesis, and performs type-checking,

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

Ltac2 Type exn ::= [ AssumeError(message) ].


Local Ltac2 expected_of_type_instead_of_message (e : constr) (t : constr) := 
  Message.concat (Message.concat 
    (Message.concat (of_string "Expected assumption of ") (of_constr e))
    (Message.concat (of_string " instead of ") (of_constr t))) (of_string ".").

(** * assume_negation
    Attempts to assume a negated expression.

    Arguments:
        - [x : (constr * (ident option)) list]: list of (expression optional name for expression)).
    Does:
        - For the first pair of (expession (and name)) in [x], 
            assume the expression.

    Raises Exceptions:
        - [AssumeError], if the current goal does not require the assumption of an expression [t]
                         where [t] is the expression from the first pair in [x].
        - [AssumeError], if [x] contains more than one element.
*)
Local Ltac2 assume_negation (x : (constr * (ident option)) list) :=
    match x with 
    | [] => () (* Done. *)
    | head::tail => 
            match head with
            | (t, n) => (* Check whether the right negated expression is assumed. *)
                    lazy_match! goal with
                    | [ |- not ?u ] => 
                            match Aux.check_constr_equal u t with
                            | false => Control.zero (AssumeError (expected_of_type_instead_of_message u t))
                            | true  => (* Check whether this was the only assumption made.*)
                                   match tail with
                                   | h::t => Control.zero (AssumeError (of_string "Nothing left to assume after the negated expression."))
                                   | [] => (* Assume negation *)
                                          (* Check whether a name has been given *)
                                          match n with
                                          | None   => let h := Fresh.in_goal @__wp__h in intro $h
                                          | Some n => intro $n
                                          end
                                   end
                            end
                    | [ |- _ ] => Control.zero (Aux.CannotHappenError "Cannot happen.")
                    end
            | _ => Control.zero (Aux.CannotHappenError "Cannot happen.")
            end
    end.

(** * process_ident_type_pairs
    Attempts to recursively assume a list of hypotheses.

    Arguments:
        - [x : (constr * (ident option)) list)]: list of (hypothesis and optional hypothesis name).
    Does:
        - For the first pair of (hypothesis (and name)) in [x], 
            assume the hypothesis (with specified name).
          If the assumed hypothesis did not come from a negated expression,
          proceeds to call itself with the remaining pairs in [x] as a new list [x'].

    Raises Exceptions:
        - [AssumeError], if the current goal does not require the assumption of any more hypotheses
                       in general or one of type [t], where [t] is the type from the first pair in [x].
*)
Local Ltac2 rec process_ident_type_pairs (x : (constr * (ident option)) list) :=
    match x with
    | head::tail =>
            match head with
            | (t, n) => lazy_match! goal with
                    (* Check whether next assumption (i.e. [t]) is that of a negated expression. *)
                    | [ |- not _ ]   => assume_negation x (* If so, switch to different subroutine. *)
                    | [ |- ?u -> _ ] => 
                            (* Check whether the domain is a proposition. *)
                            let sort_u := Aux.get_value_of_hyp u in
                            match Aux.check_constr_equal sort_u constr:(Prop) with
                            | true =>
                                (* Check whether we need variabled of type t. *)
                                match Aux.check_constr_equal u t with
                                | true =>
                                    (* Check whether a name has been given *)
                                    match n with
                                    | None   => let h := Fresh.in_goal @__wp__h in intro $h
                                    | Some n => intro $n
                                    end
                                | false => Control.zero (AssumeError (expected_of_type_instead_of_message u t))
                                end
                            | false => Control.zero (AssumeError (of_string "‘Assume’ cannot be used to construct a map (→). Use ‘Take’ instead."))
                            end
                    | [ |- _ ] => Control.zero (AssumeError (of_string "Tried to assume too many properties."))
                    end
            | _ => Control.zero (Aux.CannotHappenError "Cannot happen.")
            end;
            (* Attempt to introduce remaining variables of (different) types. *)
            process_ident_type_pairs tail
    | [] => () (* Done. *)
    end.



(** * assume
    Checks whether the 'Assume' tactic can be applied to the current goal, 
    attempts to introduce a list of hypotheses.
*)
Local Ltac2 assume (x : (constr * (ident option)) list) := 
  lazy_match! goal with
    | [ |- not _ ]  => assume_negation x
    | [ |- _ -> _ ] => process_ident_type_pairs x
    | [ |- _ ] => Control.zero (AssumeError (of_string "‘Assume’ can only be used to prove an implication (⇨) or a negation (¬)."))
  end.

(** * Assume
    Version with type checking.
*)
Ltac2 Notation "Assume" "that" x(list1(seq(constr, opt(seq("(", ident, ")"))), "and")) := 
    panic_if_goal_wrapped ();
    assume x.

(** * such that
    Simply alternative notation for [Assume].
*)
Ltac2 Notation "such" "that" x(list1(seq(constr, opt(seq("(", ident, ")"))), "and")) := 
    panic_if_goal_wrapped ();
    assume x.

