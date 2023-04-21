(** * [manipulate_negation.v]
Authors: 
    - Jelle Wemmenhove
Creation date: 2 Nov 2021

Try to prove the current goal from a hypothesis by manipulating negations, 
meaning that we interchange negations and logical operators. For example, this tactic 
can show that (¬∀x∃y∀z,P(x,y,z) implies ∃x∀y∃z, ¬P(x,y,z)).

Context specific manipulations can added by including them in the 
[global_negation_database_selection].

This tactic ([solve_by_manipulating_negation]) is added to the [classical_logic]
hint database.

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

Require Import Waterproof.auxiliary.
Require Import Waterproof.init_automation_global_variables.
Require Import Waterproof.waterprove.automation_subroutine.

(** Tactic *)
Local Ltac2 solve_by_manipulating_negation_in (h_id : ident) :=
  let h := Control.hyp h_id in
  
  (* Check whether h is a proposition. *)
  let type_h := Aux.get_value_of_hyp h in
  let sort_h := Aux.get_value_of_hyp type_h in
  match Aux.check_constr_equal sort_h constr:(Prop) with
  | false => Control.zero (NegationError "Can only manipulate negation in propositions.")
  | true => 
    let attempt () :=
      revert $h_id;
      solve[ 
        repeat (
          first [ (* finish proof *)
            exact id 
            (* without negation *)
            | lazy_match! goal with
              | [ |- (?a \/ ?b) -> (?c \/ ?d)] => apply (or_func $a $b $c $d)
              | [ |- (?a /\ ?b) -> (?c /\ ?d)] => apply (and_func $a $b $c $d)
              | [ |- (?a -> ?b) -> (?c -> ?d)] => apply (impl_func $a $b $c $d)
              (* matching on a forall statement !!! *)
              | [ |- (forall x, @?p x) -> (forall x, @?q x)] => apply (all_func _ $p $q); let x_id := Fresh.in_goal @x in intro $x_id
              | [ |- (exists x, @?p x) -> (exists x, @?q x)] => apply (ex_func _ $p $q); let x_id := Fresh.in_goal @x in intro $x_id

              (* with negation *)
              | [ |- ~(?a \/ ?b) -> (?c /\ ?d)] => apply (not_or_and_func $a $b $c $d)
              | [ |- (?c /\ ?d) -> ~(?a \/ ?b)] => apply (not_or_and_func $a $b $c $d)
              | [ |- ~(?a /\ ?b) -> (?c \/ ?d)] => apply (not_and_or_func $a $b $c $d)
              | [ |- (?c \/ ?d) -> ~(?a /\ ?b)] => apply (or_not_and_func $a $b $c $d)
              | [ |- ~(?a /\ ?b) -> (?a -> ?c)] => apply (not_and_impl_func $a $b $c)
              | [ |- (?a -> ?c) -> ~(?a /\ ?b)] => apply (impl_not_and_func $a $b $c)
              | [ |- ~(?a -> ?b) -> (?a /\ ?c)] => apply (not_impl_and_func $a $b $c)
              | [ |- (?a /\ ?c) -> ~(?a -> ?b)] => apply (and_not_impl_func $a $b $c)
              | [ |- ~(forall x, @?p x) -> (exists x, @?q x)] => apply (not_all_ex_func _ $p $q); let x_id := Fresh.in_goal @x in intro $x_id
              | [ |- (exists x, @?q x) -> ~(forall x, @?p x)] => apply (ex_not_all_func _ $p $q); let x_id := Fresh.in_goal @x in intro $x_id
              | [ |- ~(exists x, @?p x) -> (forall x, @?q x)] => apply (not_ex_all_func _ $p $q); let x_id := Fresh.in_goal @x in intro $x_id
              | [ |- (forall x, @?q x) -> ~(exists x, @?p x)] => apply (all_not_ex_func _ $p $q); let x_id := Fresh.in_goal @x in intro $x_id
              | [ |- (~~?a) -> ?b] => apply (not_neg_pos_func $a $b)
              | [ |- ?b -> (~~?a)] => apply (pos_not_neg_func $a $b)
            end
            | (* Try context specific manipulation, e.g. negating order relations *)
              let g := Control.goal () in
              let hint_databases := Some (global_negation_database_selection ()) in
              run_automation g [] 1 hint_databases false
          ] 
        ) 
      ]
      in
      match Control.case attempt with
        | Val _ => ()
        | Err exn => Control.zero (NegationError "Failed to solve by manipulating negation.")
      end
  end.


Ltac2 solve_by_manipulating_negation () :=
  match! goal with
    | [ h : _ |- _ ] => solve_by_manipulating_negation_in h
  end.

(*For debugging: do a single step *)
Local Ltac2 manipulate_negation_in (h_id : ident) :=
  let h := Control.hyp h_id in
  (* Check whether h is a proposition. *)
  let type_h := Aux.get_value_of_hyp h in
  let sort_h := Aux.get_value_of_hyp type_h in
  match Aux.check_constr_equal sort_h constr:(Prop) with
  | false => Control.zero (NegationError "Can only manipulate negation in propositions.")
  | true => 
    let attempt () :=
      revert $h_id; 
      print (of_constr (Control.goal ()));
      first [ (* finish proof *)
        exact id
        | lazy_match! goal with
                (* without negation *)
          | [ |- (?a \/ ?b) -> (?c \/ ?d)] => apply (or_func $a $b $c $d)
          | [ |- (?a /\ ?b) -> (?c /\ ?d)] => apply (and_func $a $b $c $d)
          | [ |- (?a -> ?b) -> (?c -> ?d)] => apply (impl_func $a $b $c $d)
          | [ |- (forall x, @?p x) -> (forall x, @?q x)] => apply (all_func _ $p $q); let x_id := Fresh.in_goal @x in intro $x_id
          | [ |- (exists x, @?p x) -> (exists x, @?q x)] => apply (ex_func _ $p $q); let x_id := Fresh.in_goal @x in intro $x_id

          (* with negation *)
          | [ |- ~(?a \/ ?b) -> (?c /\ ?d)] => apply (not_or_and_func $a $b $c $d)
          | [ |- (?c /\ ?d) -> ~(?a \/ ?b)] => apply (and_not_or_func $a $b $c $d)
          | [ |- ~(?a /\ ?b) -> (?c \/ ?d)] => apply (not_and_or_func $a $b $c $d)
          | [ |- (?c \/ ?d) -> ~(?a /\ ?b)] => apply (or_not_and_func $a $b $c $d)
          | [ |- ~(?a /\ ?b) -> (?a -> ?c)] => apply (not_and_impl_func $a $b $c)
          | [ |- (?a -> ?c) -> ~(?a /\ ?b)] => apply (impl_not_and_func $a $b $c)
          | [ |- ~(?a -> ?b) -> (?a /\ ?c)] => apply (not_impl_and_func $a $b $c)
          | [ |- (?a /\ ?c) -> ~(?a -> ?b)] => apply (and_not_impl_func $a $b $c)
          | [ |- ~(forall x, @?p x) -> (exists x, @?q x)] => apply (not_all_ex_func _ $p $q); let x_id := Fresh.in_goal @x in intro $x_id
          | [ |- (exists x, @?q x) -> ~(forall x, @?p x)] => apply (ex_not_all_func _ $p $q); let x_id := Fresh.in_goal @x in intro $x_id
          | [ |- ~(exists x, @?p x) -> (forall x, @?q x)] => apply (not_ex_all_func _ $p $q); let x_id := Fresh.in_goal @x in intro $x_id
          | [ |- (forall x, @?q x) -> ~(exists x, @?p x)] => apply (all_not_ex_func _ $p $q); let x_id := Fresh.in_goal @x in intro $x_id
          | [ |- (~~?a) -> ?b] => apply (not_neg_pos_func $a $b)
          | [ |- ?b -> (~~?a)] => apply (pos_not_neg_func $a $b)
          end
        | (* Try context specific manipulation, e.g. negating order relations *)
          let g := Control.goal () in
          let hint_databases := Some (global_negation_database_selection ()) in
          run_automation g [] global_search_depth hint_databases false
      ]
      in
      match Control.case attempt with
        | Val _ => ()
        | Err exn => Control.zero (exn)
      end
  end.
