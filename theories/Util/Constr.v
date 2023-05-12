Require Import Ltac2.Constr.
Require Import Ltac2.Ltac2.
Require Import Ltac2.Message.

Require Import Waterproof.Util.Init.

(** * check_constr_equal
    
  Ltac2 function: [constr -> constr -> bool]
    
  Check if the normalized form of [a] is syntactically equal to the normalized form of [b].

    Arguments:
        - [a, b: constr], any [constr]
    Returns:
        - [bool]:
            - [true] if a and b are syntactically equal
                (i.e. are of the same type after normalization)
            - [false] otherwise.
*)  
Ltac2 check_constr_equal (a: constr) (b: constr) :=
  Constr.equal (eval cbv in $a) (eval cbv in $b).

(** * ltac2_assert
    Introduce *and prove* a new sublemma.
    Wrapper for the build-in Gallina [assert] statement
    that can accept Ltac2 variables as arguments.
    Includes a 'by' clause as used in
    [assert (... : ...) by ...].

    Arguments:
        - [id: ident], name of the new sublemma to prove.
        - [lemma_content: constr], new proposition to prove.
        - [by_arg: unit -> unit], 
            function that tries the prove the new sublemma.
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

(** * ltac2_assert
    
  Introduce a new sublemma.
  
  Wrapper for the build-in Gallina [assert] statement that can accept Ltac2 variables as arguments.

  Arguments:
    - [id: ident], name of the new sublemma to prove.
    - [lemma_content: constr], new proposition to prove.
*)
Ltac2 ltac2_assert (id: ident) (lemma_content: constr) :=
  Std.assert (Std.AssertType 
    (Some (Std.IntroNaming (Std.IntroIdentifier id))) 
    lemma_content None
  ).

(** * Get coerced type on intro

  If t is a term, the following tactics allow to extract what t gets coerced to after an introduction in forall x : t, True.
    
  ** Auxiliary function to get a coerced type
    
  Returns:
    - [constr] The coercion of t if the goal is forall x : t, True.

*)
Ltac2 get_coerced_type_aux () :=
  match! goal with
    | [ |- ?c -> True ] =>  c
  end.

(** ** Get coerced type

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