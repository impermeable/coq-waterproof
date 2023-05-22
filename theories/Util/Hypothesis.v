Require Import Ltac2.Ltac2.

Require Import Util.Init.

(** get_value_of_hyp_id
    
  Given an [constr] that is the reference of a hypothesis (i.e. the LHS in the proof context, e.g. the [h] in [h: 1 + 1 = 2]), return the unnormalized value of the hypothesis.

  Arguments:
    - [hyp: constr], LHS of the hypothsis.

  Returns:
    - [constr]: unnormalized type of the hypothesis (i.e. the RHS).
*)
Ltac2 get_value_of_hyp (hyp: constr) :=
  eval unfold type_of in (type_of $hyp).

(** * get_value_of_hyp_id

  Given an [ident] matching a hypothesis, return the unnormalized value of the hypothesis.

  Arguments:
    - [hyp_id: ident], name of hypothesis.

  Returns:
    - [constr]: unnormalized type of the hypothesis.
*)
Ltac2 get_value_of_hyp_id (hyp_id: ident) :=
  let h := Control.hyp hyp_id in
  get_value_of_hyp h.