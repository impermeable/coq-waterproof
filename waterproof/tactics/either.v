(** * [either.v]
Authors: 
    - Cosmin Manea (1298542)
    - Jelle Wemmenhove

Creation date: 02 June 2021

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


Require Import Waterproof.message.
(* Database for 'Either ... or ...' tactic. *)
Require Import Waterproof.auxiliary.
Require Import Waterproof.selected_databases.
Require Import Waterproof.waterprove.automation_subroutine.
Require Export Waterproof.tactics.goal_wrappers.

Ltac2 Type exn ::= [ CaseError(string) | InputError(message) ].

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
                          match Aux.check_constr_equal v t with
                          | true => apply (Case.wrap $v)
                          | false => Control.zero (CaseError "Wrong case specified.")
                          end
                         | [|- _] => Control.zero (CaseError "No need to specify case.")
                         end.
Ltac2 Notation "Case" t(constr) := case t.


(* Switch order of decidable goal. *)
Local Lemma sumbool_comm (A B : Prop) : {A} + {B} -> {B} + {A}.
Proof. intro H. induction H. right; exact a. left; exact b. Qed.

(** * either_case_1_or_case_2
    Split the proof by case distinction.

    Arguments:
        - [t1 : constr], the first case.
        - [t2 : constr], the second case.

    Does:
        - splits the proof by case distinction; wraps the resulting goals in the Case.Wrapper
*)
Ltac2 either_or (t1:constr) (t2:constr) 
 := let hint_databases := Some (global_decidability_database_selection ()) in
    let h_id := Fresh.in_goal @h in
    let attempt () := assert ({$t1} + {$t2}) as $h_id;
                      Control.focus 1 1 (fun () => 
                        let g := Control.goal () in first 
                        [ run_automation g [] 3 hint_databases false
                        | apply sumbool_comm; run_automation g [] 3 hint_databases false
                        ])
    in
    match Control.case attempt with
    | Val _ => let h_val := Control.hyp h_id in
               destruct $h_val;
               Control.focus 1 1 (fun () => apply (Case.unwrap $t1));
               Control.focus 2 2 (fun () => apply (Case.unwrap $t2))
    | Err exn => Control.zero (CaseError "Could not find a proof that the first or the second statement holds.")
    end.

Ltac2 Notation "Either" t1(constr) "or" t2(constr) := 
    panic_if_goal_wrapped ();
    either_or t1 t2.




(* Type that enables a three-case distiction to be solved with three bullets that are of the same level. *)
Inductive sumtriad (A B C : Prop) : Set :=
  | left   : A -> sumtriad A B C
  | middle : B -> sumtriad A B C
  | right  : C -> sumtriad A B C.
Arguments left   {A B C} _.
Arguments middle {A B C} _.
Arguments right  {A B C} _.

(* Lemmas that enable the searching of hints whose cases are ordered differently than the user's input. *)
Local Lemma double_sumbool_sumtriad_abc (A B C : Prop) : {A} + {B} + {C} -> sumtriad A B C.
  Proof. intro H. induction H as [[a | b] | c]. exact (left a). exact (middle b). exact (right c). Qed.
Local Lemma double_sumbool_sumtriad_acb (A B C : Prop) : {A} + {C} + {B} -> sumtriad A B C.
  Proof. intro H. induction H as [[a | c] | b]. exact (left a). exact (right c). exact (middle b). Qed.
Local Lemma double_sumbool_sumtriad_bac (A B C : Prop) : {B} + {A} + {C} -> sumtriad A B C.
  Proof. intro H. induction H as [[b | a] | c]. exact (middle b). exact (left a). exact (right c). Qed.
Local Lemma double_sumbool_sumtriad_bca (A B C : Prop) : {B} + {C} + {A} -> sumtriad A B C.
  Proof. intro H. induction H as [[b | c] | a]. exact (middle b). exact (right c). exact (left a). Qed.
Local Lemma double_sumbool_sumtriad_cab (A B C : Prop) : {C} + {A} + {B} -> sumtriad A B C.
  Proof. intro H. induction H as [[c | a] | b]. exact (right c). exact (left a). exact (middle b). Qed.
Local Lemma double_sumbool_sumtriad_cba (A B C : Prop) : {C} + {B} + {A} -> sumtriad A B C.
  Proof. intro H. induction H as [[c | b] | a]. exact (right c). exact (middle b). exact (left a). Qed.


(** * either_case_1_or_case_2_or_case3
    Split the proof by case distinction.

    Arguments:
        - [t1 : constr], the first case.
        - [t2 : constr], the second case.
        - [t3 : constr], the third case.

    Does:
        - splits the proof by case distinction; wraps the resulting goals in the Case.Wrapper
*)
Ltac2 either_or_or (t1:constr) (t2:constr) (t3:constr)
 := let hint_databases := Some (global_decidability_database_selection ()) in
    let h_id := Fresh.in_goal @h in
    let attempt () := assert (sumtriad $t1 $t2 $t3) as $h_id;
                      Control.focus 1 1 (fun () => 
                        let g := Control.goal () in first 
                        [ apply double_sumbool_sumtriad_abc;
                          run_automation g [] 3 hint_databases false
                        | apply double_sumbool_sumtriad_acb; 
                          run_automation g [] 3 hint_databases false
                        | apply double_sumbool_sumtriad_bac; 
                          run_automation g [] 3 hint_databases false
                        | apply double_sumbool_sumtriad_bca; 
                          run_automation g [] 3 hint_databases false
                        | apply double_sumbool_sumtriad_cab; 
                          run_automation g [] 3 hint_databases false
                        | apply double_sumbool_sumtriad_cba; 
                          run_automation g [] 3 hint_databases false
                        ])
    in
    match Control.case attempt with
    | Val _ => let h_val := Control.hyp h_id in
               destruct $h_val;
               Control.focus 1 1 (fun () => apply (Case.unwrap $t1));
               Control.focus 2 2 (fun () => apply (Case.unwrap $t2));
               Control.focus 3 3 (fun () => apply (Case.unwrap $t3))
    | Err exn => Control.zero (CaseError "Could not find a proof that the first, the second or the third statement holds.")
    end.

Ltac2 Notation "Either" t1(constr) "," t2(constr) "or" t3(constr) := 
    panic_if_goal_wrapped ();
    either_or_or t1 t2 t3.
