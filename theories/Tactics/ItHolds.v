Require Import Ltac2.Ltac2.

Require Import Util.Constr.
Require Import Util.Goals.
Require Import Util.Hypothesis.
Require Import Util.Init.
Require Import Waterprove.

Local Ltac2 idtac () := ().

(**
  Introduce a new sublemma and try to prove it immediately,
  optionally using a given lemma.

  Arguments:
    - [id: ident option], optional name for the new sublemma. If the proof succeeds, it will become a hypothesis (bearing [id] as name).
    - [conclusion: constr], the actual content of the new sublemma to prove.
    - [proving_lemma: constr], optional reference to a lemma used to prove the new sublemma (via [waterprove)]).

  Raises exception:
    - [AutomationFailure], if [waterprove] fails the prove the sublemma. This happens if the sublemma does not hold, but can also happen if it is simply too difficult for [waterprove].
*)
Ltac2 assert_and_prove_sublemma (id: ident option) (conclusion: constr) (proving_lemma: constr option) :=
  let help_lemma := unwrap_optional_lemma proving_lemma in
  let by_arg () := waterprove 5 false [fun () => help_lemma] Positive in
  let proof_attempt () := (* Check whether identifier is given *)
    match id with
      | None =>
        let h := Fresh.in_goal @__wp__h in
        ltac2_assert_with_by h conclusion by_arg
      | Some id => 
        ltac2_assert_with_by id conclusion by_arg
    end
  in match Control.case proof_attempt with
    | Val _ => idtac () 
    | Err exn => Control.zero exn
  end.

(**
  Introduce a new sublemma and try to prove it immediately using a given lemma.

  Arguments:
    - [lemma: constr], reference to a lemma used to prove the new sublemma (via [waterprove)]).
    - [id: ident option], optional name for the new sublemma. If the proof succeeds, it will become a hypothesis (bearing [id] as name).
    - [conclusion: constr], the actual content of the new sublemma to prove.

    Raises exception:
    - [AutomationFailure], if [waterprove] fails the prove the sublemma. This happens if the sublemma does not hold, but can also happen if it is simply too difficult for [waterprove].
*)
Ltac2 Notation "By" lemma(constr) "it" "holds" "that" conclusion(constr) id(opt(seq("(", ident, ")"))) :=
  panic_if_goal_wrapped ();
  assert_and_prove_sublemma id conclusion (Some lemma).
    
    
(** * It holds that ... (...)
    Introduce a new sublemma and try to prove it immediately.
    Same as [By ... it holds that ... (...)],
    but without using a specified lemma.

    Arguments:
        - [id: ident option], optional name for the new sublemma.
            If the proof succeeds, 
            it will become a hypotheses (bearing [id] as name).
        - [conclusion: constr], the actual content 
            of the new sublemma to prove.

    Raises exception:
        - [AutomationFailure], if [waterprove] fails the prove the sublemma.
            This happens if the sublemma does not hold,
            but can also happen if it is simply too difficult for [waterprove].
*)
Ltac2 Notation "It" "holds" "that" conclusion(constr) id(opt(seq("(", ident, ")")))  :=
  panic_if_goal_wrapped ();
  assert_and_prove_sublemma id conclusion None.