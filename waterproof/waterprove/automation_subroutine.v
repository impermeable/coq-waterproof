(** * [waterprove.v]
Authors: 
    - Cosmin Manea (1298542)
    - Lulof Pirée (1363638)

Creation date: 01 June 2021

The automated proving functionality of coq-waterproof.
This function calls the automation tactics, [auto], [eauto], 
with a specific set of lemmas and search depth.
It is also possible to call the [intuition] Ltac1 tactic.

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

Require Import Waterproof.init_automation_global_variables.

Ltac2 Type exn ::= [ AutomationFailure(message) ].

Local Ltac2 fail_automation (t : constr option):= 
  let fail_message :=
    match t with
      | Some s => concat (concat (of_string ("Could not find a proof of ")) (of_constr s)) (of_string ".")
      | None => of_string ("Could not find a proof.")
    end
  in
  Control.zero (AutomationFailure fail_message).

(** * global_enable_intuition
    Flag whether [run_automation] and [waterprove]
    should call the [intuition] tactic on top 
    of [auto] and [new auto].
*)
Ltac2 mutable global_enable_intuition := false.

(** * global_shield_automation
    TODO
*)
Ltac2 mutable global_shield_automation := true.

(* Subroutine of [run_automation] *)
Local Ltac2 run_automation_with_intuition (search_depth: int option) (databases: ident list option) (first_lemma: constr) (lemmas: (unit -> constr) list) :=
  first [
    solve [Std.auto Std.Info search_depth lemmas databases]
    | solve [ltac1:(lemma |- intuition (info_auto using lemma with *)) (Ltac1.of_constr first_lemma)]
    | solve [ltac1:(lemma|- intuition (info_eauto using lemma with *)) (Ltac1.of_constr first_lemma)] 
    | fail_automation (Some (Control.goal()))
  ].

(* Subroutine of [run_automation] *)
Local Ltac2 run_automation_without_intuition (search_depth: int option) (databases: ident list option) (lemmas: (unit -> constr) list) :=
  first[
    solve [Std.auto global_debug_level (Some 2) lemmas databases]
    | solve [Std.auto global_debug_level search_depth lemmas databases]
    | solve [Std.eauto global_debug_level search_depth lemmas databases]
    | fail_automation (Some (Control.goal()))
  ].

(** * run_automation
    Calls the automation tactics [auto] and [new auto],
    with a specific set of lemmas, search depth and databases.
    Optionally also calls [intuition] with [auto] and [eauto],
    but with all databases, and *only the first lemma*.

    (Implementation Note:
    It was not possible to convert a [ident list] to a [constr]
    otherwise, and we can only pass [constr] to Ltac1,
    and [intuition] only exists in Ltac1)

    Arguments:
        - [prop: constr], the proposition to be proven by automation. (TODO: Incorrect!! Attempts to prove current goal)
        - [lemmas: (unit -> constr) list], list of functions mapping to
             additional lemmas to be used in the automation tactics.
             These functions take no arguments.
        - [search_depth: int], maximum search depth.
        - [hint_databases: ident list option], list of identifiers of
            registered hint databases to be used.
            If [None] given, all databases will be used
                (i.e. [auto with *]).
        - [enable_intuition: bool], flag:
            - [false], only try [auto] and [new auto].
            - [true], also try [intuition] with [auto] and with [eauto].

    Does:
        - Try to solve the goal using [auto] and [new_auto].
        - If no proof is found, print a message conveying the failure.

    Raises exceptions:
        - [AutomationFailure], if [prop] could not be proven. (TODO: Incorrect!! Attempts to prove current goal)
*)
(** Note:
    [Std.auto ] takes the following arguments:
    - [debug]. In std there is [Ltac2 Type debug := [ Off | Info | Debug ].]
        So probably a flag for debugging info?
    - [int opion], optional maximum search depth.
    - [(unit -> constr) list], list of additional lemmas to use.
    - [ident list option], optional list of database names:
        - [with *] -> use the argument [None]
        - Default (i.e. use core) -> use the argument [Some ([])]
        - Actual list of idents (wrapped in [Some]) -> 
            use the databases in the list.
        Evidence: see [test/reverse_engineer/auto_hintdb_arg.v].

    [Std.eauto] takes a second [int option] argument.
    In [Notations.v] it is called [p], but its meaning is unknown.
    Maybe the maximum allowed number of existential variables
    it may introduce?

    [Std.new_auto] takes the same arguments as [auto],
    and is also available as the tactic [new auto].


    * Options for databases:
    
*)
Ltac2 run_automation (prop: constr) (lemmas: (unit -> constr) list) (search_depth: int) (hint_databases: ident list option) (enable_intuition: bool) :=
  let result () :=
    let search_depth := Some search_depth in
    let first_lemma :=
      match lemmas with
        | head::remainder => head ()
        | [] => constr:(I) (*dummy lemma I : True*)
      end
    in 
    match enable_intuition with
      | true => run_automation_with_intuition search_depth hint_databases first_lemma lemmas
      | false => run_automation_without_intuition search_depth hint_databases lemmas
    end
  in 
  match Control.case result with
      | Val _ => ()
      | Err exn => fail_automation (Some (Control.goal()))
  end.