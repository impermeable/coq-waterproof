(** * [assume.v]
Authors: 
    - Lulof Pirée (1363638)
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
Require Import Waterproof.tactics.take.
Require Import Waterproof.tactics.goal_wrappers.

Ltac2 Type exn ::= [ AssumeError(string) ].

Ltac2 raise_assume_error (s:string) := 
    Control.zero (AssumeError s).


Local Ltac2 cannot_happen () :=
    Control.throw (Aux.CannotHappenError 
                "This statement should never be executed.").


(*
--------------------------------------------------------------------------------
    [intro_hyp_from_list] plus subroutines.
    This function is a subroutine of [Assume] itself.
*)



(* Subroutine of intro_hyp_from_list:
    performs iteration over the list [x],
    in a recursive way.
    [prev] are the previously seen items of [x],
    and [x] will be the remaining items. *)
Local Ltac2 rec intro_hyp_from_list_recursion
    (x: (ident*constr) list) (h: ident) (prev: (ident*constr) list) :=
    match x with
    | tuple::remainder => 
        match tuple with
        | (s, t) =>
            let h_constr := Control.hyp h in
            let h' := (eval cbv in (Aux.type_of $h_constr)) in
            let t' := (eval cbv in $t) in
            match (Constr.equal h' t' ) with
                | true => Std.rename ((h, s)::[]);
                    (* The type of remainder may be the empty list,
                        so we cannot simply return "remainder::prev"*)
                    match remainder with
                        | head::tail => List.append remainder prev
                        | [] => prev
                    end
                | false => 
                    intro_hyp_from_list_recursion remainder h ((s, t)::prev)
            end
        (* x is a nonempty list of (ident*constr) tuples. 
            Hence case can never happen! But Ltac2 requires it.*)
        | _ => cannot_happen ()
        end
    | [] => raise_assume_error("Premise not present in given hypotheses")
    end.

(** * intro_hyp_from_list
    Given a list of [(ident, constr)] tuples and a hypothesis [h],
    searches the list if it contains an entry [(s, t)]
    such that [t] judgementally equals the type of [h].
    As soon as such a tuple is found, [h] is renamed to [s],
    and a copy of the list with with matching [(s, t)] tuple removed
    is be returned.

    Arguments:
        - [x: (ident*constr) list], a list tuples, 
            which are pairs (hypothesis name, hypothesis type).
        - [h: ident], the ident of a hypothesis in the current context.
            [Control.hyp h] should exist.

    Returns:
        - [(ident*constr) list], a copy [x'] of [x], such [(s, t) ∉ x'], 
            where [(s, t) ∈ x] is the first entry in [x] such that
            [t] is judgementally equal to [Control.hyp h].

    Raises Exceptions:
        * [AssumeError], if there exists no [(s, t) ∈ x] such that
            [t] is judgementally equal to [Control.hyp h].
*)
Ltac2 intro_hyp_from_list (x: (ident*constr) list) (h: ident) :=
    intro_hyp_from_list_recursion x h [].


(*
--------------------------------------------------------------------------------
    Function to check if a hypothesis is in a list.
    Very similar to "intro_hyp_from_list", but does not do renaming
    nor removing elements from the list.
*)

(** * hyp_is_in_list
    Given a list of [(ident, constr)] tuples and a hypothesis [h],
    searches the list if it contains an entry [(s, t)]
    such that [t] judgementally equals the type of [h].

    Arguments:
        - [x: (ident*constr) list], a list tuples, 
            which are pairs (hypothesis name, hypothesis type).
        - [h: ident], the ident of a hypothesis in the current context.
            [Control.hyp h] should exist.

    Returns:
        - [bool],
            - [true] if such a tuple [(s, t)], where [t] matches
            the definition of [h], is found
            - [false] otherwise
*)
Ltac2 rec hyp_is_in_list (x: (ident*constr) list) (h: ident) :=
    match x with
    | head::tail =>
        match head with
        | (s, t) => 
            let h_value := Control.hyp h in
            let h' := (eval cbv in (Aux.type_of $h_value)) in
            let t' := (eval cbv in $t) in
            match (Constr.equal h' t' ) with
            | true => true
            | false => hyp_is_in_list tail h
            end
        | _ => cannot_happen ()
        end
    | [] => false
    end.

(*
--------------------------------------------------------------------------------
*)(** *    Main function implementing [Assume] plus subroutines.
*)

(* Subroutine of [assume_breakdown]*)
Ltac2 rec elim_hyp_from_list (x: (ident*constr) list) (h: ident) :=
    (* let f := fun () =>  (intro_hyp_from_list x h) in  *)
    match hyp_is_in_list x h with
    | true => intro_hyp_from_list x h
    | false =>
        (* [h] is not in the list [x]. But we know that [h] is of the form
        [h = h1 /\ h2], so check if h1 or h2 are in [x].
        If they are not but can be broken down further, 
        recursively try to do so (e.g. if [h1 = h1' /\ h1'']).
        *)
        let h1 := Fresh.in_goal h in
        (* The goal does not include h1,
            so we manually need to tell that h2 cannot be h1 *)
        let h2 := Fresh.fresh (Fresh.Free.union 
                                (Fresh.Free.of_goal ()) 
                                (Fresh.Free.of_ids (h1::[]))
                              ) h in
        let h_val := Control.hyp h in
        (destruct $h_val as [$h1 $h2];
        (* Check if we succeed in eliminating [h1] from [x].
            If not, that [h1] is unresolved, 
            and the recursive breakdown failed *)
        let x' := elim_hyp_from_list x h1 in
        match Int.equal (List.length x') (List.length x) with
        | true => raise_assume_error 
            ("Cannot be broken down: first case not covered")
        | false =>
            match x' with
            | [] => raise_assume_error (
                "Cannot break down and cover both sides: too few hypotheses")
            | head::tail => 
                let x'' := elim_hyp_from_list x' h2 in
                match Int.equal (List.length x'') (List.length x') with
                | true => raise_assume_error 
                    ("Cannot be broken down: second case not covered")
                | false => x''
                end
            end
        end)
    end.
   
(* Subroutine of [assume_premise_with_breakdown]*)
Ltac2 rec assume_breakdown (x: (ident*constr) list) :=
    match! goal with
    | [h:?a/\?b |- _] =>  
        match hyp_is_in_list x h with
        | true => let new_x := intro_hyp_from_list x h in
            match new_x with
                | head::tail => assume_breakdown new_x
                | [] => print (of_string "Hypotheses successfully assumed")
            end
        | false => assume_breakdown (elim_hyp_from_list x h)
        end
    | [|-_] => 
        match x with
        | head::tail => raise_assume_error "Too many hypotheses provided"
        | [] => print (of_string "Hypotheses successfully assumed")
        end
    end.

(* Subroutine of  [assume_premise_with_breakdown] *)
Local Ltac2 intro_one_premise_and_recurse (x: (ident*constr) list) :=
    let h := (Fresh.in_goal @h) in
    intros $h; 
    Aux.print_bool (hyp_is_in_list x h);
    elim_hyp_from_list x h; 
    print (of_string "Hypotheses successfully assumed").

(* Subroutine of  [assume_premise_with_breakdown] *)
Ltac2 intro_two_premises_and_recurse (x: (ident*constr) list) :=
    let h := @h in
    let h1 := (Fresh.in_goal h) in
    intros $h1; 
    let new_x := elim_hyp_from_list x h1 in
    let h2 := (Fresh.in_goal h) in
    intros $h2; 
    elim_hyp_from_list new_x h2;
    print (of_string "Hypotheses successfully assumed").

(** * assume_premise_with_breakdown
    Take a list of [(ident : constr)] tuples,
    where each tuple is a pair of a hypothesis name and its body.
    Try to assume all premises of the goal,
    and rename them accordingly to the input list.
    If needed to match the specified hypotheses in the list,
    automatically break down hypotheses of the form [h = h1 /\ h2]
    into [h1] and [h2]. 
    If the goal is of the form [A -> B -> C] 
    break it down to hypotheses [A] and [B] with goal [C]
    before matching with and renaming according to the input list list.
    Raise an error if the input list does not cover all hypotheses,
    or if it contains too many hypotheses.
    
    Arguments:
        - [x : (ident*constr) list], list of tuples, 
            which are (hypothesis name, hypothesis body) pairs.
  
    Raises Exceptions:
        - [AssumeError], if [x] contains too many hypotheses 
            (i.e. hypotheses that are not found 
            in the recursive breakdown).
        - [AssumeError], if [x] contains too few hypotheses 
            (i.e. the premise of the goal cannot be broken down
            such that all created hypotheses match a tuple in [x]).
*)
Ltac2 assume_premise_with_breakdown (x: (ident*constr) list) :=
    lazy_match! goal with
    | [ |- ?premise1->?premise2->?conclusion] => 
        intro_two_premises_and_recurse x
    | [ |- ?premise->?conclusion] => 
        intro_one_premise_and_recurse x
    | [ |- not ?premise] =>
        intro_one_premise_and_recurse x
    | [|- _] => raise_assume_error "Cannot assume premise: 
                                    goal is not an implication"
    end.

(** * Assume
    Version with type checking.
*)
Ltac2 Notation "Assume" x(list1(seq(ident, ":", constr), "and")) := 
    panic_if_goal_wrapped ();
    assume_premise_with_breakdown x.

(** * such that
    Simply alternative notation for [Assume].
*)
Ltac2 Notation "such" "that" x(list1(seq(ident, ":", constr), "and")) := 
    panic_if_goal_wrapped ();
    assume_premise_with_breakdown x.