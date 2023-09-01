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

Module Case.

  Private Inductive Wrapper (A G : Type) : Type :=
    | wrap : G -> Wrapper A G.
  
  Definition unwrap (A G : Type) : Wrapper A G -> G :=
    fun x => match x with wrap _ _ y => y end.

End Case.


Notation "'Add' 'the' 'following' 'line' 'to' 'the' 'proof:' 'Case' ( A )." :=
  (Case.Wrapper A _) (
    at level 99,
    only printing,
    format "'[ ' Add  the  following  line  to  the  proof: ']' '//'   Case  ( A )."
  ).

Module NaturalInduction.
  
  Module Base.
    Private Inductive Wrapper (G : Type) : Type :=
      | wrap : G -> Wrapper G.
    
    Definition unwrap (G : Type) : Wrapper G -> G :=
      fun x => match x with wrap _ y => y end.
  
  End Base.

  Module Step.
    
    Private Inductive Wrapper (G : Type) : Type :=
      | wrap : G -> Wrapper G.
    
    Definition unwrap (G : Type) : Wrapper G -> G :=
      fun x => match x with wrap _ y => y end.
  
  End Step.

End NaturalInduction.

Notation "'Add' 'the' 'following' 'line' 'to' 'the' 'proof:' 'We' 'first' 'show' 'the' 'base' 'case,' 'namely' ( G )." := 
  (NaturalInduction.Base.Wrapper G) (
    at level 99,
    only printing,
    format "'[ ' Add  the  following  line  to  the  proof: ']' '//'   We  first  show  the  base  case,  namely  ( G )."
  ).

Notation "'Add' 'the' 'following' 'line' 'to' 'the' 'proof:' 'We' 'now' 'show' 'the' 'induction' 'step.'" :=
  (NaturalInduction.Step.Wrapper _) (
    at level 99,
    only printing,
    format "'[ ' Add  the  following  line  to  the  proof: ']' '//'   We  now  show  the  induction  step."
  ).

Module ExpandDef.

  Module Goal.
  
    Private Inductive Wrapper (G : Type) : Type :=
      | wrap : G -> Wrapper G.
    
    Definition unwrap (G : Type) : Wrapper G -> G :=
      fun x => match x with wrap _ y => y end.
  
  End Goal.

  Module Hyp.
  
    Private Inductive Wrapper (G H : Type) (h : H) : Type :=
      | wrap : G -> Wrapper G H h.
    
    Definition unwrap (G H : Type) (h : H) : Wrapper G H h -> G :=
      fun x => match x with wrap _ _ _ y => y end.
  
  End Hyp.

End ExpandDef.

Notation "'Add' 'the' 'following' 'line' 'to' 'the' 'proof:' 'That' 'is,' 'write' 'the' 'goal' 'as' '(' G ').'" :=
  (ExpandDef.Goal.Wrapper G) (
    at level 99,
    only printing,
    format "'[ ' Add  the  following  line  to  the  proof: ']' '//'   That  is,  write  the  goal  as  ( G )."
  ).

Notation "'Add' 'the' 'following' 'line' 'to' 'the' 'proof:' 'That' 'is,' 'write' '(' h ')' 'as' '(' H ').'" :=
  (ExpandDef.Hyp.Wrapper _ H h) (
    at level 99,
    only printing,
    format "'[ ' Add  the  following  line  to  the  proof: ']' '//'   That  is,  write  ( h )  as  ( H )."
  ).

Module StateGoal.
  
  Private Inductive Wrapper (G : Type) : Type :=
    | wrap : G -> Wrapper G.
  
  Definition unwrap (G : Type) : Wrapper G -> G :=
    fun x => match x with wrap _ y => y end.

End StateGoal.

Notation "'Add' 'the' 'following' 'line' 'to' 'the' 'proof:' 'We' 'need' 'to' 'show' 'that' '(' G ').' 'or' 'write:' 'We' 'conclude' 'that' '(' G ').' 'if' 'no' 'intermediary' 'proof' 'steps' 'are' 'required.'" :=
  (StateGoal.Wrapper G) (
    at level 99,
    only printing,
    format "'[ ' Add  the  following  line  to  the  proof: ']' '//'   We  need  to  show  that  ( G ). '//' or  write: '//'   We  conclude  that  ( G ). '//' if  no  intermediary  proof  steps  are  required."
  ).

Module ByContradiction.

  Private Inductive Wrapper (A G : Type) : Type :=
    | wrap : G -> Wrapper A G.
  
  Definition unwrap (A G : Type) : Wrapper A G -> G :=
    fun x => match x with wrap _ _ y => y end.

End ByContradiction.

Notation "'Add' 'the' 'following' 'line' 'to' 'the' 'proof:' 'Assume' 'that' '(' A ').'" :=
  (ByContradiction.Wrapper A _) (
    at level 99,
    only printing,
    format "'[ ' Add  the  following  line  to  the  proof: ']' '//'   Assume  that  ( A )."
  ).


Ltac2 raise_goal_wrapped_error () := 
  throw (of_string "You cannot do this right now, follow the advice in the goal window.").


(**
  Throws an error if the goal is wrapped in one of the wrappers above.

  Arguments:  None
*)
Ltac2 panic_if_goal_wrapped () :=
  lazy_match! goal with
    | [|- Case.Wrapper _ _]                => raise_goal_wrapped_error ()
    | [|- NaturalInduction.Base.Wrapper _] => raise_goal_wrapped_error ()
    | [|- NaturalInduction.Step.Wrapper _] => raise_goal_wrapped_error ()
    | [|- ExpandDef.Goal.Wrapper _]        => raise_goal_wrapped_error ()
    | [|- ExpandDef.Hyp.Wrapper _ _ _]     => raise_goal_wrapped_error ()
    | [|- StateGoal.Wrapper _]             => raise_goal_wrapped_error ()
    | [|- ByContradiction.Wrapper _ _]     => raise_goal_wrapped_error ()
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
      match check_constr_equal v t with
        | true => apply (Case.wrap $v)
        | false => throw (of_string "Wrong case specified.")
      end
    | [|- _] => throw (of_string "No need to specify case.")
  end.

Ltac2 Notation "Case" t(constr) := case t.