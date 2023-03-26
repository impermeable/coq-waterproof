(** * [waterprove.v]
Authors: 
    - Cosmin Manea (1298542)
    - Lulof Pirée (1363638)

Creation date: 01 June 2021

The waterprove automation function.
This function calls the automation subroutine [run_automation]
with a specific set of lemmas and search depth.
It is also possible to call the [intuition] Ltac1 tactic.
Optionally, certain goals can be shielded, i.e. they are not shown automatically.

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


Require Import Waterproof.message.

Require Import Waterproof.definitions.inequality_chains.
Require Import Waterproof.selected_databases.
Require Import Waterproof.waterprove.automation_subroutine.
Require Import Waterproof.waterprove.manipulate_negation.

Local Ltac2 fail_automation (t : constr option):= 
        let first_part_message :=
            match t with
            | Some s => concat (of_string ("Waterproof could not find a proof of "))
                               (of_constr s)
            | None => of_string ("Waterproof could not find a proof")
            end
        in 
        let fail_message :=
            concat first_part_message
                   (of_string ("  ... If you believe the statement should hold, 
try making a smaller step."))
        in
        Control.zero (AutomationFailure fail_message).

(** * waterprove
    Calls the automation subroutine [run_automation]
    with a specific set of lemmas.
    
    Uses the databases encoded 
    in the global variable [global_database_selection]. 
    Uses the maximum search depth stored 
    in the global variable [global_search_depth].

    Arguments:
        - [prop: constr], the proposition to be proven by automation. (TODO: Incorrect!! Attempts to prove current goal)
        - [lemmas: (unit -> constr) list], list of functions mapping to
             additional lemmas to be used in the automation tactics.
             These functions take no arguments.
        - [shield: bool], whether to shield certain goals from being shown automatically.

    Does:
        - Try to solve the goal using [run_automation] with [lemmas].
        - If no proof is found, print a message conveying the failture.

    Raises exceptions:
        - [AutomationFailure], if [prop] could not be proven. (TODO: Incorrect!! Attempts to prove current goal)
*)

Local Ltac2 actual_waterprove (prop: constr) (lemmas: (unit -> constr) list) (shield:bool) :=
    let first_attempt () := run_automation prop lemmas 3 (Some (global_first_attempt_database_selection ())) false
    in
    let second_attempt () := 
        match shield with
            | true => match global_shield_automation with
                       | true => (* Match goal with basic logical operators *)
                               lazy_match! goal with
                               | [ |- forall _, _ ] => fail_automation None
                               | [ |- exists _, _ ] => fail_automation None
                               | [ |- _ /\ _] => fail_automation None
                               | [ |- _ \/ _] => fail_automation None
                               | [ |- _] => ()
                               end
                       | false => ()
                       end
            | false => ()
            end;
            let databases :=
                match global_use_all_databases with
                | true => None
                | false => Some (global_database_selection ())
                end
            in
            run_automation prop lemmas global_search_depth 
                           databases global_enable_intuition
    in 
    match Control.case first_attempt with
    | Val _ => ()
    | Err exn => 
        match Control.case second_attempt with
        | Val _ => ()
        | Err exn => fail_automation (Some (Control.goal()))
        end
    end.


Ltac2 waterprove (prop: constr) (lemmas: (unit -> constr) list) (shield:bool) :=
  (* Splits chain of inequalities into its parts and calls the actual waterprove subroutine on those. *)
  lazy_match! goal with
  | [ |- total_statement _ ] => repeat split;
                                Control.enter (fun () => 
                                  cbn;
                                  actual_waterprove prop lemmas shield
                                )
  | [ |- _] => actual_waterprove prop lemmas shield
  end.

