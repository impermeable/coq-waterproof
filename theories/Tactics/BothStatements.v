(******************************************************************************)
(*                  This file is part of Waterproof-lib.                      *)
(*                                                                            *)
(*   Waterproof-lib is free software: you can redistribute it and/or modify   *)
(*    it under the terms of the GNU General Public License as published by    *)
(*     the Free Software Foundation, either version 3 of the License, or      *)
(*                    (at your option) any later version.                     *)
(*                                                                            *)
(*     Waterproof-lib is distributed in the hope that it will be useful,      *)
(*      but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*       MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the         *)
(*               GNU General Public License for more details.                 *)
(*                                                                            *)
(*     You should have received a copy of the GNU General Public License      *)
(*   along with Waterproof-lib. If not, see <https://www.gnu.org/licenses/>.  *)
(*                                                                            *)
(******************************************************************************)

Require Import Ltac2.Ltac2.
Require Import Ltac2.Message.
Local Ltac2 concat_list (ls : message list) : message :=
  List.fold_right concat (of_string "") ls.

Require Import Util.Constr.
Require Import Util.Goals.
Require Import Util.MessagesToUser.

(**
  Split the proof of a conjuction statement into both of its parts, wraps both the resulting goals in a [StateGoal.Wrapper].

  Arguments:
    - no arguments

  Does:
    - splits the conjunction statement into its both parts.
    - wraps both goals in a [StateGoal.Wrapper].

  Raises fatal exceptions:
    - If the [goal] is not a conjunction of statments.
*)
Ltac2 both_directions_and () :=
  lazy_match! goal with 
    | [ |- _ /\ _] => split; Control.enter (fun () => apply StateGoal.unwrap)
    | [ |- _ ] => throw (of_string "This is not an 'and' statement, so try another approach.")
  end.

Ltac2 Notation "We" "show" "both" "statements" := 
  panic_if_goal_wrapped ();
  both_directions_and ().

Ltac2 Notation "We" "prove" "both" "statements" := 
  panic_if_goal_wrapped ();
  both_directions_and ().

Local Ltac2 need_to_show_instead_of_msg (correct:constr) (wrong:constr) :=
  concat_list [of_string "You need to show "; of_constr correct;
    of_string " instead of "; of_constr wrong; of_string "."].
(**
  Split the proof of a conjuction statement into two specified parts, but also verifies that the parts wrote by the user, in which the goal should split into, are the correct ones.

  Arguments:
    - [s: constr], the first part given.
    - [t: constr], the second part given.

  Does:
    - Splits the [goal] into [s /\ t] or [t /\ s], if the goal can be written as such a conjuction.
    - If it cannot be written, it prints a statement saying what the respective part that does not match should actually be.
    - If the goal is of the form [t /\ s], it is changed to [s /\ t] before splitting.

  Raises fatal exceptions:
    - If the [goal] is not a conjunction of the specified statments.
*)
Ltac2 both_directions_and_with_types (s: constr) (t:constr) :=
  lazy_match! goal with
    | [ |- ?u /\ ?v] => (* Check if s matches the first part *)
      match check_constr_equal s u with
        | true  =>
          match check_constr_equal t v with
            | true  => split
            | false => throw (need_to_show_instead_of_msg v t)
          end
        | false => (* Otherwise, check if it matches the second part *)
          match check_constr_equal s v with 
            | true =>
              match check_constr_equal t u with 
                | true  =>
                  apply and_comm; (* i.e. switch order *)
                  split
                | false => throw (need_to_show_instead_of_msg u t)
              end
            | false => (* If s does not match anything, check if t matches something *)
              match check_constr_equal t u with 
                | true  => throw (need_to_show_instead_of_msg v s)
                | false =>
                  match check_constr_equal t v with 
                    | true  => throw (need_to_show_instead_of_msg u s)
                    | false => throw (of_string "Neiher of these two statements are what you need to show.")
                  end
              end
          end
      end
    | [ |- _ ] => throw (of_string "This is not an 'and' statement, so try another tactic.")
  end.


Ltac2 Notation "We" "show" "both" s(constr) "and" t(constr) :=
  panic_if_goal_wrapped ();
  both_directions_and_with_types s t.

Ltac2 Notation "We" "prove" "both" s(constr) "and" t(constr) :=
  panic_if_goal_wrapped ();
  both_directions_and_with_types s t.


