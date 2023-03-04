(** * [rewrite_inequalities.v]
Authors: 
    - Lulof Pirée (1363638)
Creation date: 10 June 2021

Tactics used to rewrite inequalities involving ≤, <, >,	≥, etc.
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

Require Import Reals.

Require Import Waterproof.tactics.forward_reasoning.rewrite_using.
Require Import Waterproof.string_auxiliary.
Require Import Waterproof.auxiliary.
Require Import Waterproof.tactics.forward_reasoning.forward_reasoning_aux.
Require Import Waterproof.tactics.goal_wrappers.

Open Scope R_scope.

(* For throwing erros in a [first] block.
    There errors will always be converted to
    [Tactic_failure], 
    so no message can really be used. *)
Local Ltac2 fail_rewrite () :=
    Control.zero (RewriteError "").

(** * Abstract algorithm description
    The following is an example of the purpose
    and method of the algotithm that the tactic [Rewrite]
    implements.

    Suppose one has the goal [A < E] 
    and knows that [A < B < C < D < E].
    Now one wants to rewrite the goal to [D < E].
    This can be done as follows:

    By transitivty, we know that [A < B] and [B < C]
    implies [A < C].
    Then, from [C < D], it follows that [A < D].
    Finally we use [D < E] to derive [A < E]. Qed.

    Note that the reasoning takes place from left to right
    (from the goal towards the first hypothesis [A < B]),
    and at each step the 'chain' is shortened:
    - Step 0: [A < B < C < D < E] Goal: [A < E]
    - Step 1: [B < C < D < E] Goal : [B < E]
    - Step 2: [C < D < E] Goal: [C < E]
    - Step 3: [D < E] Goal : [D < E]
    Also note that, at every step, three propositions are involved:
    [x < y] (First remaining inequality in the chain),
    [x < z] (old goal)
    and
    [y < z] (new goal).
    This is confusing at first, but in Coq one often proves
    goals 'backward' (start at the conclusion, 
    and in reverse order prove all the steps that lead to it).
    It makes sense when seen in the following way:
    - In Coq, transitivity has the form [(x < y) -> (y < z) -> (x < z)].
    - We know [x < y], so by ⇒-elim, we derive [(y < z) -> (x < z)].
    - Hence to prove [x < z], it suffices to show that [y < z], 
        which becomes the new goal.

    In the Ltac1 implementation, 
    the 'head' of the chain ([A < ...]) 
    remains the goal throughout execution of the algorithm.
    Also in this implementation, all inequalities are variables.
*)

Ltac2 Type Inequality := [
    | Less
    | LessEq
    | Greater
    | GreaterEq
    | Eq
].

Ltac2 Type Chain := [
    | ChainEnd
    | ChainLink (constr * Inequality * constr)
].


(** * string_to_ineq_rec
    Subroutine of [string_to_ineq].
    Compare [str] to each element of [candidates].
    If they are equal, return the element of
    [ineqs] at the same index. If they are all different,
    raise an [RewriteError].

    Arguments:
        - [str: string], string to compare to candidate-strings.
        - [candidates: string list], list of strings to which
            [str] is to be compared.
        - [ineqs: Inequality list], list of same length
            as [candidates]. 
    
    Returns:
        - [Inequality], the element of [ineqs].
            If [str] equals some element
            at [candiates] index [i], then the element
            at index of [ineqs] will be returned.
    
    Raises exceptions:
        - [RewriteError], if [str] does not match
            any element of [candidates].
        - [CannotHappenError], if [candidates] does not have
            the same length as [ineqs].
*)
Local Ltac2 rec string_to_ineq_rec (str: string) 
                             (candidates: string list) 
                             (ineqs: Inequality list) :=
    
    match ineqs with
    | ineq::ineqs_remainder =>
        match candidates with
        | head::candidates_remainder =>
            match string_equal str head with
            | true => ineq
            | false =>  
                string_to_ineq_rec str candidates_remainder 
                                   ineqs_remainder
            end
        | [] =>  
            Aux.cannot_happen "[ineqs] must have same length as [candidates]"
        end
    | [] => Control.zero (RewriteError "Invalid (in)equality connective")
    end.

(** * string_to_ineq
    Match a string representation to the corresponding [Inequality].
    Supported strings: ["<", "<=", "≤", ">", "≥", ">=", "="].

    Argumens:
        - [str: string], string to find equality for.

    Returns:
        - [Inequality], the inequality described by the string.
    
    Raises exceptions:
        - [RewriteError], if [str] does not match
            any element of ["<", "<=", "≤", ">", "≥", ">=", "="].
*)
Ltac2 string_to_ineq (str: string) :=
    let candidates := "<"::"<="::"≤"::">"::"≥"::">="::"="::[] in
    let ineqs := Less::LessEq::LessEq::Greater::GreaterEq::GreaterEq::Eq::[] in
    string_to_ineq_rec str candidates ineqs.

(** * convert_to_chain 

    Base cases:
        - [rest] is [None] (B1) or an empty list (B2). 
            Then add ChainEnd to the [chain], reverse the result,
            and return it.

    Recursive case:
        - RC:
            Let [A] be [head], and [("<", B)::[]] be [rest].
            Add [ChainLink A Less B] to the head of chain,
            remove [("<", B)] from [rest],
            make [B] the new [head],
            and recurse (the next recursion will be a terminal base case).
*)
Ltac2 rec convert_to_chain (head: constr) 
                           (rest: (string * constr) list option)
                           (chain: Chain list) :=
    match rest with
    
    | None => 
        (* Base case B1 *)
        let result := (ChainEnd)::chain
        in (List.rev result) 
    | Some rest_list => 
        match rest_list with
        
        | rest_first::remainder => 
            (* Recursive case RC *)
            match rest_first with
            | (str, rhs_expr) =>
                let ineq := string_to_ineq str in   
                let link := ChainLink (head, ineq, rhs_expr) in
                convert_to_chain rhs_expr (Some remainder) (link::chain)
            | _ => Aux.cannot_happen ""
            end
        
        | [] => 
            (* Base case B2 *)
            let result := (ChainEnd)::chain
            in (List.rev result)
        end
    end.

(** * gen_prop_from_link
    Converts the value of a [ChainLink] to the corresponding [constr].

    Arguments:
        - [link: constr * Inequality * constr], encoding of (in)equality.
            Must be converible to a proposition of the form [x R y],
            where [x] matches the [x] in the goal.
            The first [constr] ([x]) is the LHS variable, 
            and the last [constr] ([y]) is the RHS variable.

    Returns:
        - [constr], (in)equality of form [x R y], 
            made from the corresponding Gallina notation
            of the [Inequality] in link, and [x] and [y].

    Raises exceptions:
        - [CannotHappenError], if the [link] is not convertible
            to an (in)equality-type [constr]
*)
Local Ltac2 gen_prop_from_link (link : constr * Inequality * constr) :=
    match link with
    | (a, ineq, b) => 
        match ineq with
        | Less => constr:($a < $b)
        | LessEq => constr:($a <= $b)
        | Greater => constr:($a > $b)
        | GreaterEq => constr:($a >= $b)
        | Eq => constr:($a = $b)
        | _ => Aux.cannot_happen ""
        end
    | _ => Aux.cannot_happen ""
    end.

(** * rewrite_last_link
    Subroutine of [rewrite_single_inequality].

    Precondition:
    Let [R] and [R'] be relations in {<, <=, =, =>, >}.
        - The last link in the chain has been proven as some hypothesis [h],
            and has the form [h := a R b].
        - The goal is [a R' b] (for the same [a] and [b]).

    Does:
        - Try to prove the goal using [h]. 
        This may include rewriting [h] into a weaker form first
        (e.g. change [<] into [<=], or [=] into [>=]).

    Raises exceptions:
        - [RewriteError], if the goal cannot be proven using [h].
*)
Local Ltac2 rewrite_last_link () :=
    first [
      apply Rlt_le; assumption
    | apply Rlt_gt; assumption
    | apply Rgt_ge; assumption
    | apply Rgt_lt; assumption
    | apply Req_le; assumption
    | apply Req_ge; assumption
    | assumption 
    | print (of_string  
        "Same terms as goal, but cannot rewrite the relation");
        fail_rewrite ()
    ].

(** * rewrite_less_link
    Subroutine of [rewrite_single_inequality].

    Precondition:
        - Current link has been proven as [h], and has form [x < y].
        - Goal has form [x < z] or [x <= z].

    Arguments:
        - [h: ident], name of hypothesis that states [x < y].
        - [x, y, z: constr], variables in inequalities.

    Does:
        - Rewrite goal to [y <= z].

    Raises exceptions:
        - [RewriteError], if the goal cannot be rewritten to [y <= z].
*)
Local Ltac2 rewrite_less_link (h: ident) (x: constr) (y: constr) (z: constr) :=
    let h_val := Control.hyp h in
    first [   
          apply (Rlt_le $x $y) in $h; apply (Rle_trans $x $y $z $h_val)
        | apply (Rlt_le_trans $x $y $z $h_val)
        | apply (Rle_lt_trans $x $y $z $h_val)
        | print (of_string "'<' does not work here.");
        print (of_string "with ");
        print (of_constr h_val);
        print (of_string "and goal ");
        print (of_constr (Control.goal ()));
        fail_rewrite ()
    ].

(** * rewrite_less_equal_link
    Subroutine of [rewrite_single_inequality].

    Precondition:
        - Current link has been proven as [h], and has form [x <= y].
        - Goal has form [x < z] or [x <= z].

    Arguments:
        - [h: ident], name of hypothesis that states [x <= y].
        - [x, y, z: constr], variables in inequalities.

    Does:
        - Rewrite goal to [y <= z].

    Raises exceptions:
        - [RewriteError], if the goal cannot be rewritten to [y <= z].
*)
Local Ltac2 rewrite_less_equal_link (h: ident) (x: constr) 
                                    (y: constr) (z: constr) :=
    let h_val := Control.hyp h in
    first [ 
        apply (Rle_trans $x $y $z $h_val)
        | apply (Rle_trans $x $y $z (Rlt_le $x $y $h_val))
        | print (of_string  "'≤' does not work here.");
        fail_rewrite ()
    ].

(** * rewrite_greater_link
    Subroutine of [rewrite_single_inequality].

    Precondition:
        - Current link has been proven as [h], and has form [x > y].
        - Goal has form [x > z] or [x >= z].

    Arguments:
        - [h: ident], name of hypothesis that states [x > y].
        - [x, y, z: constr], variables in inequalities.

    Does:
        - Rewrite goal to [y >= z].

    Raises exceptions:
        - [RewriteError], if the goal cannot be rewritten to [y >= z].
*)
Local Ltac2 rewrite_greater_link (h: ident) (x: constr) 
                                    (y: constr) (z: constr) :=
    let h_val := Control.hyp h in
    first [   
          apply (Rgt_ge $x $y) in $h; apply (Rge_trans $x $y $z $h_val)
        | apply (Rge_gt_trans $x $y $z $h_val)
        | apply (Rgt_ge_trans $x $y $z $h_val)
        | print (of_string  "'>' does not work here.");
            fail_rewrite ()
    ].

(** * rewrite_greater_equal_link
    Subroutine of [rewrite_single_inequality].

    Precondition:
        - Current link has been proven as [h], and has form [x >= y].
        - Goal has form [x > z] or [x >= z].

    Arguments:
        - [h: ident], name of hypothesis that states [x >= y].
        - [x, y, z: constr], variables in inequalities.

    Does:
        - Rewrite goal to [y >= z].

    Raises exceptions:
        - [RewriteError], if the goal cannot be rewritten to [y >= z].
*)
Local Ltac2 rewrite_greater_equal_link (h: ident) (x: constr) 
                                    (y: constr) (z: constr) :=
    let h_val := Control.hyp h in
    first [ 
          apply (Rge_trans $x $y $z $h_val)
        | apply (Rge_trans $x $y $z (Rge_trans $x $y $h_val))
        | print (of_string "'≥' does not work here.");
            fail_rewrite ()
    ].

(** * rewrite_equality_link
    Subroutine of [rewrite_single_inequality].

    Precondition:
        - Current link has been proven as [h], and has form [x = y].
        - Goal has form [x = z].

    Arguments:
        - [h: ident], name of hypothesis that states [x = y].

    Does:
        - Rewrite goal to [y = z].

    Raises exceptions:
        - [RewriteError], if the goal cannot be rewritten to [y = z].
*)
Local Ltac2 rewrite_equality_link (h: ident) :=
    let h_val := Control.hyp h in
    first [ 
          rewrite <- $h_val
        | rewrite $h_val
        | print (of_string "'=' does not work here.");
            fail_rewrite ()
        ].

(** * rewrite_single_inequality
    Subroutine of [rewrite_chain_rec].

    Precondition:
        - Goal has form [x R z] for some relation [R] in {<, <=, =, =>, >}.

    Arguments:
        - [link : constr * Inequality * constr], 
            (in)equality proposition used to rewrite or prove the goal.
            Must be converible to a proposition of the form [x R y],
            where [x] matches the [x] in the goal.
            The first [constr] is the LHS variable, 
            and the last [constr] is the RHS variable.

    Does:
        - If [y] is not [z], rewrite goal to [y R' z], where [R'] is:
            - [<=] in case [R] in the the goal is [<] or [<=].
            - [>=] in case [R] in the the goal is [>] or [>=].
            - [=] in case [R] in the the goal is [=].
        - Prove the goal in case [y] is [z].

    Raises exceptions:
        - [RewriteError], if the goal cannot be rewritten or proven.
        - [CannotHappenError], if [link] cannot be converted.
        - [AutomationFailure], if the proposition encoded by [link]
            cannot be proven by automation.
*)
Local Ltac2 rewrite_single_inequality (link : constr * Inequality * constr) :=
    let prop := gen_prop_from_link link in
    let h := Fresh.in_goal @h in
    let by_arg () := waterprove_without_hint prop constr:(dummy_lemma) true
    in
    let verify_prop () := Aux.ltac2_assert_with_by h prop by_arg
    in
    match Control.case verify_prop with
    | Val _ => 
        lazy_match! goal with
        | [|- ?symbol ?x ?z ] =>
            match link with
            | (x', ineq, y) => 
                match Constr.equal x x' with
                | true => 
                match Constr.equal y z with
                    | true => rewrite_last_link ()
                    | false => 
                        match ineq with
                        | Less => rewrite_less_link h x y z
                        | LessEq => rewrite_less_equal_link h x y z
                        | Greater => rewrite_greater_link h x y z
                        | GreaterEq => rewrite_greater_equal_link h x y z
                        | Eq => rewrite_equality_link h
                        | _ => Aux.cannot_happen ""
                        end;
                        clear $h
                    end
                | false => Control.throw (RewriteError 
                    "LHS of (in)equality must match LHS of goal.")
                end
            | _ => Aux.cannot_happen ""
            end
        end
    | Err exn => fail_verify_prop ()
    end.

(* Subroutine of [rewrite_chain] *)
Local Ltac2 rec rewrite_chain_rec (chain: Chain list) :=
    match chain with
    | head::remainder =>
        match head with
        | ChainEnd => ()
        | ChainLink link => 
            let f () := rewrite_single_inequality link
            in
            match Control.case f with
            | Val _ => rewrite_chain_rec remainder
            | Err exn => 
                print (of_string "Got error: ");
                print (of_exn exn);
                Control.zero 
                (RewriteError "Failed to rewrite (in)equality")
            end
        | _ => Aux.cannot_happen ""
        end
    | [] => Aux.cannot_happen "Chain should end with [ChainEnd]."
    end.

(** * rewrite_chain
    Given a goal [x_1 R x_n] and a chain of (in) equality propositions 
    [x_1 R_1 x_2 ... R_{k-1} x_k], 
    where each [R_i] is a relation in {<, <=, =, =>, >},
    try to prove the goal, or rewrite the goal to [x_{k} R' x_n].

    Precondition:
        - Goal has form [x R z] for some relation [R] in {<, <=, =, =>, >}.

    Arguments:
        [chain: Chain list]: list of Chain instances 
            that encode the chained (in)equality [x_1 R_1 x_2 ... R_{k-1} x_k].
            The last element must be [ChainEnd],
            all other elements must be [ChainLink]s.
    
    Does:
        - Check all propositions encoded in [Chain] 
            (and remove them from context before termination).
        - If [k] = [n], prove the goal
        - If [k] ≠ [n], rewrite the goal to [x_{k} R' x_n].

    Raises exceptions:
        - [RewriteError], if the goal cannot be rewritten or proven.
        - [AutomationFailure], if any proposition encoded 
            by a [ChainLink] in [chain] cannot be proven by automation.
*)
Ltac2 rewrite_chain (chain : Chain list) :=
    rewrite_chain_rec chain.


(** Reqrite inequality
    See [rewrite_chain] above for functional description.
    
    Arguments:
        - [head: constr], a variable [x_1] that is the first term in 
            [x_1 R_1 x_2 ... R_{k-1} x_k].
        - [rest: string * constr list], list of string-constr pairs
            that encode expressions [R_{i-1}, x_i].
            The [string]s must be one of {"<", "<=", "≤", ">", "≥", ">=", "="}.


    Example syntax:
        - [Rewrite inequality 1 < 2 = 2 <= 3 < 4]
    *)
(* The [tactic] synthetic class is also used for strings,
    according to the reference manual.
    https://coq.inria.fr/refman/proof-engine/ltac2.html#syntactic-classes
*)
Ltac2 Notation "Rewrite" "inequality" head(constr) rest(list0(seq(tactic(0), constr))) := 
    panic_if_goal_wrapped ();
    let chain := convert_to_chain head (Some rest) []
    in rewrite_chain chain.

(* Just alternative notation for the above. Note that it misses "in-". *)
Ltac2 Notation "Rewrite" "equality" head(constr) rest(list0(seq(tactic(0), constr))) := 
    panic_if_goal_wrapped ();
    let chain := convert_to_chain head (Some rest) []
    in rewrite_chain chain.
