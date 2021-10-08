(** * [either.v]
Authors: 
    - Cosmin Manea (1298542)
    - Jelle Wemmenhove

Creation date: 02 June 2021
Latest edit:   07 Oct 2021

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
(* Database for 'Either ... or ...' tactic. *)
Require Import Waterproof.tactics.automation_databases.decidability_db.
Require Import Waterproof.tactics.goal_wrappers.

Ltac2 Type exn ::= [ CaseError(string) ].
Ltac2 raise_case_error (s:string) := Control.zero (CaseError s).


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
                          | false => raise_case_error("Wrong case specified.")
                          end
                         | [|- _] => raise_case_error("No need to specify case.")
                         end.

Ltac2 Notation "Case" t(constr) := case t.

