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
  Definition unwrapwrap {A G : Type} {x : G} : unwrap _ _ (wrap A G x) = x
             := eq_refl.
  Definition wrapunwrap {A G : Type} {x : Wrapper A G} : wrap A G (unwrap _ _ x) = x
             := match x with wrap _ _ y => eq_refl end.
End Case.
Notation "'Add' '‘Case' (  A ).’ 'to' 'proof' 'script.'" 
         := (Case.Wrapper A _) (at level 99, only printing).

Module NaturalInduction.
  Module Base.
    Private Inductive Wrapper (G : Type) : Type :=
      | wrap : G -> Wrapper G.
    Definition unwrap (G : Type) : Wrapper G -> G 
               := fun x => match x with wrap _ y => y end.
    Definition unwrapwrap {G : Type} {x : G} : unwrap _ (wrap G x) = x
               := eq_refl.
    Definition wrapunwrap {G : Type} {x : Wrapper G} : wrap G (unwrap _ x) = x
               := match x with wrap _ y => eq_refl end.
  End Base.

  Module Step.
    Private Inductive Wrapper (G : Type) : Type :=
      | wrap : G -> Wrapper G.
    Definition unwrap (G : Type) : Wrapper G -> G 
               := fun x => match x with wrap _ y => y end.
    Definition unwrapwrap {G : Type} {x : G} : unwrap _ (wrap G x) = x
               := eq_refl.
    Definition wrapunwrap {G : Type} {x : Wrapper G} : wrap G (unwrap _ x) = x
               := match x with wrap _ y => eq_refl end.
  End Step.
End NaturalInduction.
Notation "'Add' '‘We' 'first' 'show' 'the' 'base' 'case,' 'namely' (  G ).’ 'to' 'proof' 'script.'" 
         := (NaturalInduction.Base.Wrapper G) (at level 99, only printing).
Notation "'Add' '‘We' 'now' 'show' 'the' 'induction' 'step.’' 'to' 'proof' 'script.'"
         := (NaturalInduction.Step.Wrapper _) (at level 99, only printing).

Module ExpandDef.
  Module Goal.
    Private Inductive Wrapper (G : Type) : Type :=
      | wrap : G -> Wrapper G.
    Definition unwrap (G : Type) : Wrapper G -> G 
               := fun x => match x with wrap _ y => y end.
    Definition unwrapwrap {G : Type} {x : G} : unwrap _ (wrap G x) = x
               := eq_refl.
    Definition wrapunwrap {G : Type} {x : Wrapper G} : wrap G (unwrap _ x) = x
               := match x with wrap _ y => eq_refl end.
  End Goal.

  Module Hyp.
    Private Inductive Wrapper (G H : Type) (h : H) : Type :=
      | wrap : G -> Wrapper G H h.
    Definition unwrap (G H : Type) (h : H) : Wrapper G H h -> G 
               := fun x => match x with wrap _ _ _ y => y end.
    Definition unwrapwrap {G H : Type} {h : H} {x : G} : unwrap _ _ _ (wrap G H h x) = x
               := eq_refl.
    Definition wrapunwrap {G H : Type} {h : H} {x : Wrapper G H h} : wrap G H h (unwrap _ _ _ x) = x
               := match x with wrap _ _ _ y => eq_refl end.
  End Hyp.
End ExpandDef.
Notation "'Add' '‘That' 'is,' 'write' 'the' 'goal' 'as' (  G ).’ 'to' 'proof' 'script.'" 
         := (ExpandDef.Goal.Wrapper G) (at level 99, only printing).
Notation "'Add' '‘That' 'is,' 'write' h 'as' (  H ).’ 'to' 'proof' 'script.'" 
         := (ExpandDef.Hyp.Wrapper _ H h) (at level 99, only printing).

Module StateGoal.
  Private Inductive Wrapper (G : Type) : Type :=
    | wrap : G -> Wrapper G.
  Definition unwrap (G : Type) : Wrapper G -> G 
             := fun x => match x with wrap _ y => y end.
  Definition unwrapwrap {G : Type} {x : G} : unwrap _ (wrap G x) = x
             := eq_refl.
  Definition wrapunwrap {G : Type} {x : Wrapper G} : wrap G (unwrap _ x) = x
             := match x with wrap _ y => eq_refl end.
End StateGoal.
Notation "'Add' '‘We' 'need' 'to' 'show' 'that' (  G ).’ 'to' 'proof' 'script.'" 
         := (StateGoal.Wrapper G) (at level 99, only printing).


Ltac2 Type exn ::= [ GoalWrappedError(string) ].
Ltac2 raise_goal_wrapped_error () := Control.zero (GoalWrappedError(
  "You cannot do this right now, follow the advice in the goal window.")).

Ltac2 idtac () := ().


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
     | [|- _] => idtac ()
     end.



