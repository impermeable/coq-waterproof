(** * [induction.v]
Author: 
    - Cosmin Manea (1298542)
    - Jelle Wemmenhove

Creation date: 06 June 2021
Latest edit:   07 Oct 2021

Tactic for proving by mathematical induction.
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

Require Import Waterproof.auxiliary.
Require Import Waterproof.debug.
Require Export Waterproof.tactics.goal_wrappers.

Ltac2 Type exn ::= [ NaturalInductionError(string) ].
Ltac2 raise_natind_error (s:string) := Control.zero (NaturalInductionError s).

(* Lemma to write Sn in goal induction step as n+1. *)
Lemma Sn_eq_nplus1 : forall n, S n = n + 1.
Proof. intro n. induction n. reflexivity. simpl. rewrite IHn. reflexivity. Qed.

(** * induction_with_hypothesis_naming
    Performs mathematical induction.

    Arguments:
        - [x: ident], the variable to perform the induction on.

    Does:
        - performs induction on [x]. If [x] is a natural number, the first goal is wrapped in 
          NaturalInduction.Base.Wrapper and the second goal is wrapped in
          NaturalInduction.Step.Wrapper.
*)
Ltac2 induction_without_hypothesis_naming (x: ident) :=    
  match Control.case (fun () => Control.hyp x) with
    | Val x => ()
    | Err _ => intros $x
  end;
  let x_hyp := Control.hyp x in
  let type_x := (Aux.get_value_of_hyp x_hyp) in
  match (Constr.equal type_x constr:(nat)) with
    | true => let ih_x := Fresh.in_goal @IH in
      induction $x_hyp as [ | $x $ih_x]; 
      Control.focus 1 1 (fun () => apply (NaturalInduction.Base.unwrap));
      Control.focus 2 2 (fun () => revert $ih_x; rewrite (Sn_eq_nplus1 $x_hyp); apply (NaturalInduction.Step.unwrap))
    | false => induction $x_hyp
  end.

Ltac2 Notation "We" "use" "induction" "on" x(ident) :=
  debug_ident "induction" "x" x;
  panic_if_goal_wrapped ();
  induction_without_hypothesis_naming x.

(** *
    Removes the NaturalInduction.Base.Wrapper.

    Arguments:
        - [t : constr], goal that is wrapped

    Does:
        - removes the NaturalInduction.Base.Wrapper from the goal

    Raises Exceptions:
        - [NaturalInductionError], if the [goal] is the type [t] wrapped in the base case wrapper, 
          i.e. the goal is not of the form [NaturalInduction.Base.Wrapper t].
*)
Ltac2 base_case (t:constr) :=
  lazy_match! goal with
    | [|- NaturalInduction.Base.Wrapper ?v] =>
      match Constr.equal v t with
        | true => apply (NaturalInduction.Base.wrap)
        | false => raise_natind_error("Wrong goal specified.")
      end
    | [|- _] => raise_natind_error("No need to indicate showing a base case.")
  end.

Ltac2 Notation "We" "first" "show" "the" "base" "case," "namely" that(opt("that")) t(constr) :=
  debug "induction_base_base" "start";
  base_case t.

(** *
    Removes the NaturalInduction.Step.Wrapper.

    Arguments: none

    Does:
        - removes the NaturalInduction.Step.Wrapper from the goal

    Raises Exceptions:
        - [NaturalInductionError], if the [goal] is not wrapped in the induction step case wrapper, 
          i.e. the goal is not of the form [NaturalInduction.Step.Wrapper G] for some type [G].
*)
Ltac2 induction_step () := 
  lazy_match! goal with
    | [|- NaturalInduction.Step.Wrapper _] => apply (NaturalInduction.Step.wrap)
    | [|- _] => raise_natind_error("No need to indicate showing an induction step.")
  end.

Ltac2 Notation "We" "now" "show" "the" "induction" "step" := 
  debug "induction_step" "start";
  induction_step ().
