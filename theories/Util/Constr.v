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

Require Import Ltac2.Constr.
Require Import Ltac2.Ltac2.
Require Import Ltac2.Message.

Require Import Util.Init.
Require Import Util.TypeCorrector.

(** 
  Ltac2 function: [constr -> constr -> bool]
    
  Check if the normalized form of [a] is syntactically equal to the normalized form of [b].

  Arguments:
    - [a, b: constr], any [constr]
   
  Returns:
    - [bool]: indicating it if a and b are syntactically equal (i.e. are of the same type after normalization)
*)  
Ltac2 check_constr_equal (a: constr) (b: constr) :=
  Constr.equal (eval cbv in $a) (eval cbv in $b).

(**
  Introduce *and prove* a new sublemma.
    
  Wrapper for the build-in Gallina [assert] statement that can accept Ltac2 variables as arguments.
    
  Includes a 'by' clause as used in [assert (... : ...) by ...].

  Arguments:
    - [id: ident], name of the new sublemma to prove.
    - [lemma_content: constr], new proposition to prove.
    - [by_arg: unit -> unit], function that tries the prove the new sublemma.
*)
Ltac2 ltac2_assert_with_by (id: ident) (lemma_constent: constr) (by_arg: unit -> unit) :=
  (* 
    [Std.assert] expects an [AssertType] as argument.
    An [AssrtType] consist of three parts:
      - [intropatterns opt]: the whole [(Some (Std.IntroNaming (Std.IntroIdentifier id)))] thing just wraps an [ident] into an optional [intropatterns].
      - [constr]: the actual propositions to assert.
      - [(unit -> unit) option]: the method to prove the proposition (e.g. manually done with "by [something]"). It is a series of tactic executions used to prove the [constr].
  *)
  Std.assert (Std.AssertType 
    (Some (Std.IntroNaming (Std.IntroIdentifier id))) 
    lemma_constent (Some by_arg)
  ).

(** 
  Introduce a new sublemma.
  
  Wrapper for the build-in Gallina [assert] statement that can accept Ltac2 variables as arguments.

  Arguments:
    - [id: ident], name of the new sublemma to prove.
    - [lemma_content: constr], new proposition to prove.
*)
Ltac2 ltac2_assert (id: ident) (lemma_content: constr) :=
  let lemma_content := correct_type_by_wrapping lemma_content in
  Std.assert (Std.AssertType 
    (Some (Std.IntroNaming (Std.IntroIdentifier id))) 
    lemma_content None
  ).

(**
  If t is a term, the following tactics allow to extract what t gets coerced to after an introduction in forall x : t, True.
    
  ** Auxiliary function to get a coerced type
    
  Returns:
    - [constr] The coercion of t if the goal is forall x : t, True.

*)
Ltac2 get_coerced_type_aux () :=
  match! goal with
    | [ |- ?c -> True ] =>  c
  end.

(**
  If t is a term, the following tactic allows to extract what t gets coerced to after an introduction in forall x : t, True.

  Arguments:
    - [t : constr] The term to be coerced

  Returns:
    - [constr] The coerced term after introduction in forall x : t, True.
*)
Ltac2 get_coerced_type (t : constr) :=
  let dummy_hyp := Fresh.fresh (Fresh.Free.of_goal ()) @dummy_hypothesis in 
  ltac2_assert (dummy_hyp) constr:(forall _ : $t, True);
  
  (* 
    The previous line creates an extra goal, which causes multiple goals to focus.
    Goal matching panics on this, so we need to refocus on the first goal.
  *)
  let z := Control.focus 1 1 (get_coerced_type_aux) in
  Control.focus 1 1 (fun () => exact (fun x => I)); (* prove the lemma *)
  clear $dummy_hyp; (* clear the resulting hypothesis *)
  z.