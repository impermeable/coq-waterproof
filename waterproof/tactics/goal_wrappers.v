From Ltac2 Require Import Ltac2.
From Ltac2 Require Import Message.
Ltac2 msg x := print (of_string x).

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
Notation "'Add' '‘We' 'first' 'show' 'the' 'base' 'case,' 'i.e.' 'that' (  G ).’ 'to' 'proof' 'script.'" 
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


Ltac2 Type exn ::= [ GoalWrappedError(string) ].
Ltac2 raise_goal_wrapped_error () := Control.zero (GoalWrappedError(
  "You cannot do this right now, follow the advice in the goal window.")).

Ltac2 idtac () := ().

Ltac2 panic_if_goal_wrapped () 
  := lazy_match! goal with
     | [|- Case.Wrapper _ _]                => raise_goal_wrapped_error ()
     | [|- NaturalInduction.Base.Wrapper _] => raise_goal_wrapped_error ()
     | [|- NaturalInduction.Step.Wrapper _] => raise_goal_wrapped_error ()
     | [|- ExpandDef.Goal.Wrapper _]        => raise_goal_wrapped_error ()
     | [|- ExpandDef.Hyp.Wrapper _ _ _]     => raise_goal_wrapped_error ()
     | [|- _] => idtac ()
     end.

(*
Ltac2 panic_and_test () := panic_if_goal_wrapped (); reflexivity.
Ltac2 Notation testtac := panic_if_goal_wrapped (); reflexivity.


Require Import Waterproof.auxiliary.
Ltac2 induction_without_hypothesis_naming (x: ident) :=
    let x_val := Control.hyp x in 
      let type_x := eval cbv in (Aux.type_of $x_val) in
        match (Constr.equal type_x constr:(nat)) with
        | true => induction $x_val; Control.focus 1 1 (fun () => apply (NaturalInduction.Base.unwrap));
                                    Control.focus 2 2 (fun () => apply (NaturalInduction.Step.unwrap))
        | false => induction $x_val
        end.
Ltac2 Notation "We" "use" "induction" "on" x(ident) := 
    induction_without_hypothesis_naming x.

(** Test 0: This should work *)
Goal forall n : nat, n + 0 = n.
    intro n.
    We use induction on n.
    testtac.
Abort.
*)




