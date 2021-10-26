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
From Ltac2 Require Import Message.
(* Database for 'Either ... or ...' tactic. *)
Require Import Waterproof.tactics.automation_databases.decidability_db.
Require Import Waterproof.auxiliary.
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
:= let h := Fresh.in_goal @h in
   (* Try to find a proof of t1 + t2. *)
   let attempt_proof1 () := (assert ({$t1} + {$t2}) as $h 
        by (auto with decidability nocore)) in
   match Control.case attempt_proof1 with
    | Val _   => destruct h; 
                 Control.focus 1 1 (fun () => apply (Case.unwrap $t1));
                 Control.focus 2 2 (fun () => apply (Case.unwrap $t2))
    | Err exn => (* If not found, try to find a proof of t2 + t1. *)
                 let attempt_proof2 () := (assert ({$t1} + {$t2}) as $h 
                      by (apply sumbool_comm; auto with decidability nocore)) in
                 match Control.case attempt_proof2 with
                 | Val _   => destruct h; 
                              Control.focus 1 1 (fun () => apply (Case.unwrap $t1));
                              Control.focus 2 2 (fun () => apply (Case.unwrap $t2))
                 | Err exn => Control.zero exn (*(CaseError "Could not find a proof that at least the first or the second statement holds.")*)
                 end
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
:= let h := Fresh.in_goal @h in
   (* Try to find a proof of t1 + t2 + t3. *)
   let attempt_proof_abc () := (assert (sumtriad $t1 $t2 $t3) as $h 
        by (apply double_sumbool_sumtriad_abc; auto with decidability nocore)) in
   match Control.case attempt_proof_abc with
    | Val _ => destruct h; 
               Control.focus 1 1 (fun () => apply (Case.unwrap $t1));
               Control.focus 2 2 (fun () => apply (Case.unwrap $t2));
               Control.focus 3 3 (fun () => apply (Case.unwrap $t3))
    | Err exn
      => (* Try to find a proof of t1 + t3 + t2. *)
          let attempt_proof_acb () := (assert (sumtriad $t1 $t2 $t3) as $h 
              by (apply double_sumbool_sumtriad_acb; auto with decidability nocore)) in
          match Control.case attempt_proof_acb with
          | Val _ => destruct h; 
                     Control.focus 1 1 (fun () => apply (Case.unwrap $t1));
                     Control.focus 2 2 (fun () => apply (Case.unwrap $t2));
                     Control.focus 3 3 (fun () => apply (Case.unwrap $t3))
          | Err exn
            => (* Try to find a proof of t2 + t1 + t3. *)
                let attempt_proof_bac () := (assert (sumtriad $t1 $t2 $t3) as $h 
                    by (apply double_sumbool_sumtriad_bac; auto with decidability nocore)) in
                match Control.case attempt_proof_bac with
                | Val _ => destruct h; 
                           Control.focus 1 1 (fun () => apply (Case.unwrap $t1));
                           Control.focus 2 2 (fun () => apply (Case.unwrap $t2));
                           Control.focus 3 3 (fun () => apply (Case.unwrap $t3))
                | Err exn
                  => (* Try to find a proof of t2 + t3 + t1. *)
                let attempt_proof_bca () := (assert (sumtriad $t1 $t2 $t3) as $h 
                          by (apply double_sumbool_sumtriad_bca; auto with decidability nocore)) in
                      match Control.case attempt_proof_bca with
                      | Val _ => destruct h; 
                                 Control.focus 1 1 (fun () => apply (Case.unwrap $t1));
                                 Control.focus 2 2 (fun () => apply (Case.unwrap $t2));
                                 Control.focus 3 3 (fun () => apply (Case.unwrap $t3))
                      | Err exn
                        => (* Try to find a proof of t3 + t1 + t2. *)
                            let attempt_proof_cab () := (assert (sumtriad $t1 $t2 $t3) as $h 
                                by (apply double_sumbool_sumtriad_cab; auto with decidability nocore)) in
                            match Control.case attempt_proof_cab with
                            | Val _ => destruct h; 
                                       Control.focus 1 1 (fun () => apply (Case.unwrap $t1));
                                       Control.focus 2 2 (fun () => apply (Case.unwrap $t2));
                                       Control.focus 3 3 (fun () => apply (Case.unwrap $t3))
                            | Err exn
                              => (* Try to find a proof of t3 + t2 + t1. *)
                                  let attempt_proof_cba () := (assert (sumtriad $t1 $t2 $t3) as $h 
                                      by (apply double_sumbool_sumtriad_cba; auto with decidability nocore)) in
                                  match Control.case attempt_proof_cba with
                                  | Val _ => destruct h; 
                                             Control.focus 1 1 (fun () => apply (Case.unwrap $t1));
                                             Control.focus 2 2 (fun () => apply (Case.unwrap $t2));
                                             Control.focus 3 3 (fun () => apply (Case.unwrap $t3))
                                  | Err exn => Control.zero (CaseError "Could not find a proof that at least the first, the second or the third statement holds.")
                                  end
                            end
                      end
                end
          end
    end.

Ltac2 Notation "Either" t1(constr) "," t2(constr) "or" t3(constr) := 
    panic_if_goal_wrapped ();
    either_or_or t1 t2 t3.
