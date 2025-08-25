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

Require Import Util.Constr.
Require Import Util.MessagesToUser.
Require Import Util.TypeCorrector.

Local Ltac2 concat_list (ls : message list) : message :=
  List.fold_right concat (of_string "") ls.

(* Note that the verbiage in this file is used to tweak behaviour in waterproof-vscode *)
(* In partiular the phrases "Add the following line to the proof:" and "or write:" are *)
(* used as markers to show buttons to adopt suggestions. *)

Module Case.

  Private Inductive Wrapper (A G : Type) : Type :=
    | wrap : G -> Wrapper A G.

  Definition unwrap (A G : Type) : Wrapper A G -> G :=
    fun x => match x with wrap _ _ y => y end.

  (* Add new function that combines wrapping with messaging *)
  Ltac2 wrap_with_message (case_type : constr) (goal_type : constr) :=
    apply (Case.wrap $case_type $goal_type).

End Case.


Notation "'Add' 'the' 'following' 'line' 'to' 'the' 'proof:' '-' 'Case' A ." :=
  (Case.Wrapper A _) (
    at level 99,
    only printing,
    format "'[ ' Add  the  following  line  to  the  proof: ']' '//' '//' -  Case  A ."
  ).

Module NaturalInduction.

  Module Base.
    Private Inductive Wrapper (G : Type) : Type :=
      | wrap : G -> Wrapper G.

    Definition unwrap (G : Type) : Wrapper G -> G :=
      fun x => match x with wrap _ y => y end.

    (* Add new function that combines wrapping with messaging *)
    Ltac2 wrap_with_message (goal_type : constr) :=
      apply (NaturalInduction.Base.wrap $goal_type).
  End Base.

  Module Step.

    Private Inductive Wrapper (G : Type) : Type :=
      | wrap : G -> Wrapper G.

    Definition unwrap (G : Type) : Wrapper G -> G :=
      fun x => match x with wrap _ y => y end.

    (* Add new function that combines wrapping with messaging *)
    Ltac2 wrap_with_message (goal_type : constr) :=
      apply (NaturalInduction.Step.wrap $goal_type).
  End Step.

End NaturalInduction.

Notation "'Add' 'the' 'following' 'line' 'to' 'the' 'proof:' '-' 'We' 'first' 'show' 'the' 'base' 'case' G ." :=
  (NaturalInduction.Base.Wrapper G) (
    at level 99,
    only printing,
    format "'[ ' Add  the  following  line  to  the  proof: ']' '//' '//' -  We  first  show  the  base  case  G ."
  ).

Notation "'Add' 'the' 'following' 'line' 'to' 'the' 'proof:' 'We' 'now' 'show' 'the' 'induction' 'step.'" :=
  (NaturalInduction.Step.Wrapper _) (
    at level 99,
    only printing,
    format "'[ ' Add  the  following  line  to  the  proof: ']' '//' '//' We  now  show  the  induction  step."
  ).


Module StateGoal.

  Private Inductive Wrapper (G : Type) : Type :=
    | wrap : G -> Wrapper G.

  Definition unwrap (G : Type) : Wrapper G -> G :=
    fun x => match x with wrap _ y => y end.

  (* Add new function that combines wrapping with messaging *)
  Ltac2 wrap_with_message (goal_type : constr) :=
    apply (StateGoal.wrap $goal_type).

End StateGoal.

Notation "'Add' 'the' 'following' 'line' 'to' 'the' 'proof:' 'We' 'need' 'to' 'show' 'that' G '.' 'or' 'write:' 'We' 'conclude' 'that' G '.' 'if' 'no' 'intermediary' 'proof' 'steps' 'are' 'required.'" :=
  (StateGoal.Wrapper G) (
    at level 99,
    only printing,
    format "'[ ' Add  the  following  line  to  the  proof: ']' '//' '//' We  need  to  show  that  G . '//' '//' or  write: '//' '//' We  conclude  that  G . '//' '//' if  no  intermediary  proof  steps  are  required."
  ).

Module VerifyGoal.

  Private Inductive Wrapper (G : Type) : Type :=
    | wrap : G -> Wrapper G.

  Definition unwrap (G : Type) : Wrapper G -> G :=
    fun x => match x with wrap _ y => y end.

  (* Add new function that combines wrapping with messaging *)
  Ltac2 wrap_with_message (goal_type : constr) :=
    apply (VerifyGoal.wrap $goal_type).

End VerifyGoal.

Notation "'Add' 'the' 'following' 'line' 'to' 'the' 'proof:' '{' 'Indeed,' G '.' '}' 'or' 'write:' '{' 'We' 'need' 'to' 'verify' 'that' G '.' '}' 'if' 'intermediary' 'proof' 'steps' 'are' 'required.'" :=
  (VerifyGoal.Wrapper G) (
    at level 99,
    only printing,
    format "'[ ' Add  the  following  line  to  the  proof: ']' '//' '//' {  Indeed,  G .  } '//' '//' or  write: '//' '//' {  We  need  to  verify  that  G . '//' '//' } '//' '//' if  intermediary  proof  steps  are  required."
  ).


Module StateHyp.

  Private Inductive Wrapper (A : Type) (h : A) (G : Type) : Type :=
    | wrap : G -> Wrapper A h G.

  Definition unwrap (A : Type) (h : A) (G : Type) : Wrapper A h G -> G :=
    fun x => match x with wrap _ _ _ y => y end.

  (* Add new function that combines wrapping with messaging *)
  Ltac2 wrap_with_message (hyp_type : constr) (h : constr) (goal_type : constr) :=
    apply (StateHyp.wrap $hyp_type $h $goal_type).

End StateHyp.

Notation "'Add' 'the' 'following' 'line' 'to' 'the' 'proof:' 'It' 'holds' 'that' A '.'" :=
  (StateHyp.Wrapper A _ _) (
    at level 99,
    only printing,
    format "'[ ' Add  the  following  line  to  the  proof: ']' '//' '//' It  holds  that  A ."
  ).

Module ByContradiction.

  Private Inductive Wrapper (A G : Type) : Type :=
    | wrap : G -> Wrapper A G.

  Definition unwrap (A G : Type) : Wrapper A G -> G :=
    fun x => match x with wrap _ _ y => y end.

  (* Add new function that combines wrapping with messaging *)
  Ltac2 wrap_with_message (assumption_type : constr) (goal_type : constr) :=
    apply (ByContradiction.wrap $assumption_type $goal_type).

End ByContradiction.

Notation "'Add' 'the' 'following' 'line' 'to' 'the' 'proof:' 'Assume' 'that' A '.'" :=
  (ByContradiction.Wrapper A _) (
    at level 99,
    only printing,
    format "'[ ' Add  the  following  line  to  the  proof: ']' '//' '//' Assume  that  A ."
  ).


Module StrongIndIndxSeq.

  Module Base.
    Private Inductive Wrapper (G : Type) : Type :=
    | wrap : G -> Wrapper G.

    Definition unwrap (G : Type) : Wrapper G -> G :=
      fun x => match x with wrap _ y => y end.

    (* Add new function that combines wrapping with messaging *)
    Ltac2 wrap_with_message (goal_type : constr) :=
      apply (StrongIndIndxSeq.Base.wrap $goal_type).
  End Base.

  Module Step.
    Private Inductive Wrapper (G : Type) : Type :=
      | wrap : G -> Wrapper G.

    Definition unwrap (G : Type) : Wrapper G -> G :=
      fun x => match x with wrap _ y => y end.

    (* Add new function that combines wrapping with messaging *)
    Ltac2 wrap_with_message (goal_type : constr) :=
      apply (StrongIndIndxSeq.Step.wrap $goal_type).
  End Step.

End StrongIndIndxSeq.

Notation "'Add' 'the' 'following' 'line' 'to' 'the' 'proof:' '-' 'We' 'first' 'define' 'n_0' '.'" :=
  (StrongIndIndxSeq.Base.Wrapper _) (
    at level 99,
    only printing,
    format "'[ ' Add  the  following  line  to  the  proof: ']' '//' '//' -  We  first  define  n_0 ."
  ).

Notation "'Add' 'the' 'following' 'line' 'to' 'the' 'proof:' 'Take' 'k' '∈' 'ℕ' 'and' 'assume' 'n_0,...,n_k' 'are' 'defined.'" :=
  (StrongIndIndxSeq.Step.Wrapper _) (
    at level 99,
    only printing,
    format "'[ ' Add  the  following  line  to  the  proof: ']' '//' '//' Take  k  ∈  ℕ  and  assume  n_0,...,n_k  are  defined."
  ).


Ltac2 raise_goal_wrapped_error () :=
  throw (of_string "You cannot do this right now, follow the advice in the goal window.").

(** 
  Provide template hints for wrapped goals 
*)
Ltac2 goal_wrapped_template_msg () : bool :=
  lazy_match! goal with
  | [|- Case.Wrapper ?case_type _] => 
    replace_notice (Message.to_string (concat_list [of_string "- Case "; of_constr case_type; of_string ".${0}"])); true
  | [|- StateGoal.Wrapper ?goal_type] => 
    replace_notice (Message.to_string (concat_list [of_string "We need to show that "; of_constr goal_type; of_string ".${0}"]));
    replace_notice (Message.to_string (concat_list [of_string "We conclude that "; of_constr goal_type; of_string ".${0}"])); true
  | [|- VerifyGoal.Wrapper ?goal_type] => 
    replace_notice (Message.to_string (concat_list [of_string "{ Indeed, "; of_constr goal_type; of_string ". }${0}"]));
    replace_notice (Message.to_string (concat_list [of_string "{ We need to verify that "; of_constr goal_type; of_string ". }${0}"])); true
  | [|- StateHyp.Wrapper ?hyp_type _ _] => 
    replace_notice (Message.to_string (concat_list [of_string "It holds that "; of_constr hyp_type; of_string ".${0}"])); true
  | [|- ByContradiction.Wrapper ?assumption_type _] => 
    replace_notice (Message.to_string (concat_list [of_string "Assume that "; of_constr assumption_type; of_string ".${0}"])); true
  | [|- NaturalInduction.Base.Wrapper ?goal_type] => 
    replace_notice (Message.to_string (concat_list [of_string "- We first show the base case "; of_constr goal_type; of_string ".${0}"])); true
  | [|- NaturalInduction.Step.Wrapper _] => 
    replace_notice "- We now show the induction step.${0}"; true
  | [|- StrongIndIndxSeq.Base.Wrapper _] => 
    replace_notice "- We first define n_0.${0}"; true
  | [|- StrongIndIndxSeq.Step.Wrapper _] => 
    replace_notice "- Take k ∈ ℕ and assume n_0,...,n_k are defined.${0}"; true
  | [|- False] => true
  | [|- _] => false
  end.

Ltac2 feedback_wrapped () :=
  let _ := goal_wrapped_template_msg () in
  raise_goal_wrapped_error ().
(**
  Throws an error if the goal is wrapped in one of the wrappers above.

  Arguments:  None
*)
Ltac2 panic_if_goal_wrapped () :=
  lazy_match! goal with
    | [|- Case.Wrapper _ _]                => feedback_wrapped ()
    | [|- NaturalInduction.Base.Wrapper _] => feedback_wrapped ()
    | [|- NaturalInduction.Step.Wrapper _] => feedback_wrapped ()
    | [|- StateGoal.Wrapper _]             => feedback_wrapped ()
    | [|- VerifyGoal.Wrapper _]            => feedback_wrapped ()
    | [|- StateHyp.Wrapper _ _ _]          => feedback_wrapped ()
    | [|- ByContradiction.Wrapper _ _]     => feedback_wrapped ()
    | [|- StrongIndIndxSeq.Base.Wrapper _]      => feedback_wrapped ()
    | [|- StrongIndIndxSeq.Step.Wrapper _]      => feedback_wrapped ()
    | [|- _] => ()
  end.


(**
  Removes the Case.Wrapper.

  Arguments:
    - [t : constr], case in which the goal is wrapped

  Does:
    - removes the Case.Wrapper from the goal

  Raises Exceptions:
    - [CaseError], if the [goal] is not wrapped in the case [t], i.e. the goal is not of the form [Case.Wrapper t G] for some type [G].
*)
Ltac2 case (t:constr) :=
  lazy_match! goal with
    | [|- Case.Wrapper ?v _] =>
      let t := correct_type_by_wrapping t in
      match check_constr_equal v t with
        | true => apply (Case.wrap $v)
        | false => throw (of_string "Wrong case specified.")
      end
    | [|- _] => throw (of_string "No need to specify case.")
  end.

Ltac2 Notation "Case" t(lconstr) := case t.

(**
  A goal to remind the reader to go back to an earlier
  warning
*)

Inductive fix_earlier_warning : Prop :=.

Notation "'Fix' 'an' 'earlier' 'warning'" := fix_earlier_warning.

(**
Intended for use in combination with magic:
Adds a custom "False" as a shelved goal, so the
proof cannot be finished without removing the warning.
*)
Ltac2 assert_fix_earlier_warning () :=
  let w := Fresh.in_goal @__aux in
  assert fix_earlier_warning as $w;
  Control.focus 1 1 (fun () => admit);
  clear $w.
