(** * [goal_wrappers.v]
Authors: 
    - Jelle Wemmenhove

Creation date: 08 Oct 2021

Contains the wrappers that a goal can be wrapped in to force the user to
apply a specific tactic.
The aim of these wrappers is to keep the proof script readable without relying
on the proofview window.
Also contains a tactic that throws an exception if the goal is wrapped.
This is to be used to prevent other tactics from advancing the proof state whilst
the goal is wrapped.

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

Module Case.
  Private Inductive Wrapper (A G : Type) : Type :=
    | wrap : G -> Wrapper A G.
  Definition unwrap (A G : Type) : Wrapper A G -> G 
             := fun x => match x with wrap _ _ y => y end.
End Case.
Notation "'Add' 'the' 'following' 'line' 'to' 'the' 'proof:' 'Case' ( A )." 
         := (Case.Wrapper A _) (at level 99, only printing,
             format "'[ ' Add  the  following  line  to  the  proof: ']' '//'   Case  ( A ).").

Module NaturalInduction.
  Module Base.
    Private Inductive Wrapper (G : Type) : Type :=
      | wrap : G -> Wrapper G.
    Definition unwrap (G : Type) : Wrapper G -> G 
               := fun x => match x with wrap _ y => y end.
  End Base.

  Module Step.
    Private Inductive Wrapper (G : Type) : Type :=
      | wrap : G -> Wrapper G.
    Definition unwrap (G : Type) : Wrapper G -> G 
               := fun x => match x with wrap _ y => y end.
  End Step.
End NaturalInduction.
Notation "'Add' 'the' 'following' 'line' 'to' 'the' 'proof:' 'We' 'first' 'show' 'the' 'base' 'case,' 'namely' ( G )." 
         := (NaturalInduction.Base.Wrapper G) (at level 99, only printing,
             format "'[ ' Add  the  following  line  to  the  proof: ']' '//'   We  first  show  the  base  case,  namely  ( G ).").
Notation "'Add' 'the' 'following' 'line' 'to' 'the' 'proof:' 'We' 'now' 'show' 'the' 'induction' 'step.'" 
         := (NaturalInduction.Step.Wrapper _) (at level 99, only printing,
             format "'[ ' Add  the  following  line  to  the  proof: ']' '//'   We  now  show  the  induction  step.").

Module ExpandDef.
  Module Goal.
    Private Inductive Wrapper (G : Type) : Type :=
      | wrap : G -> Wrapper G.
    Definition unwrap (G : Type) : Wrapper G -> G 
               := fun x => match x with wrap _ y => y end.
  End Goal.

  Module Hyp.
    Private Inductive Wrapper (G H : Type) (h : H) : Type :=
      | wrap : G -> Wrapper G H h.
    Definition unwrap (G H : Type) (h : H) : Wrapper G H h -> G 
               := fun x => match x with wrap _ _ _ y => y end.
  End Hyp.
End ExpandDef.
Notation "'Add' 'the' 'following' 'line' 'to' 'the' 'proof:' 'That' 'is,' 'write' 'the' 'goal' 'as' '(' G ').'"
         := (ExpandDef.Goal.Wrapper G) (at level 99, only printing,
             format "'[ ' Add  the  following  line  to  the  proof: ']' '//'   That  is,  write  the  goal  as  ( G ).").
Notation "'Add' 'the' 'following' 'line' 'to' 'the' 'proof:' 'That' 'is,' 'write' '(' h ')' 'as' '(' H ').'"
         := (ExpandDef.Hyp.Wrapper _ H h) (at level 99, only printing,
             format "'[ ' Add  the  following  line  to  the  proof: ']' '//'   That  is,  write  ( h )  as  ( H ).").

Module StateGoal.
  Private Inductive Wrapper (G : Type) : Type :=
    | wrap : G -> Wrapper G.
  Definition unwrap (G : Type) : Wrapper G -> G 
             := fun x => match x with wrap _ y => y end.
End StateGoal.
Notation "'Add' 'the' 'following' 'line' 'to' 'the' 'proof:' 'We' 'need' 'to' 'show' 'that' '(' G ').' 'or' 'write:' 'We' 'conclude' 'that' '(' G ').' 'if' 'no' 'intermediary' 'proof' 'steps' 'are' 'required.'"
         := (StateGoal.Wrapper G) (at level 99, only printing,
             format "'[ ' Add  the  following  line  to  the  proof: ']' '//'   We  need  to  show  that  ( G ). '//' or  write: '//'   We  conclude  that  ( G ). '//' if  no  intermediary  proof  steps  are  required.").

Module ByContradiction.
  Private Inductive Wrapper (A G : Type) : Type :=
    | wrap : G -> Wrapper A G.
  Definition unwrap (A G : Type) : Wrapper A G -> G 
             := fun x => match x with wrap _ _ y => y end.
End ByContradiction.
Notation "'Add' 'the' 'following' 'line' 'to' 'the' 'proof:' 'Assume' 'that' '(' A ').'"
         := (ByContradiction.Wrapper A _) (at level 99, only printing,
             format "'[ ' Add  the  following  line  to  the  proof: ']' '//'   Assume  that  ( A ).").

Ltac2 Type exn ::= [ GoalWrappedError(string) ].
Ltac2 raise_goal_wrapped_error () := Control.zero (GoalWrappedError(
  "You cannot do this right now, follow the advice in the goal window.")).


(** * panic_if_goal_wrapped
    Throws an error if the goal is wrapped in one of the wrappers above.

    Arguments:  None
*)
Ltac2 panic_if_goal_wrapped () 
  := lazy_match! goal with
     | [|- Case.Wrapper _ _]                => raise_goal_wrapped_error ()
     | [|- NaturalInduction.Base.Wrapper _] => raise_goal_wrapped_error ()
     | [|- NaturalInduction.Step.Wrapper _] => raise_goal_wrapped_error ()
     | [|- ExpandDef.Goal.Wrapper _]        => raise_goal_wrapped_error ()
     | [|- ExpandDef.Hyp.Wrapper _ _ _]     => raise_goal_wrapped_error ()
     | [|- StateGoal.Wrapper _]             => raise_goal_wrapped_error ()
     | [|- ByContradiction.Wrapper _ _]     => raise_goal_wrapped_error ()
     | [|- _] => ()
     end.



