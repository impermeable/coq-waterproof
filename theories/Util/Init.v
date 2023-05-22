Require Import Ltac2.Ltac2.

(**
  Used to indicate that an a part of an Ltac2 function is not reachable
*)
Ltac2 Type exn ::= [ Unreachable(string) ].

(**
  Throw an <<Unreachable>> exception
*)
Ltac2 unreachable (message: string) :=
  Control.throw (Unreachable message).

(**
  Gallina function mapping a term to its type.

  Arguments:
    - [T:type], any type
    - [x:T], a term of a generic type T.
  Returns:
    - [T], the type of x.
*)
Definition type_of {T : Type} (x : T) := T.

(**
  Given an optional lemma, either returns the lemma itself, or case the argument is [None], returns a dummy lemma (I : True).

  Arguments:
    - [lemma: constr option], one of the following:
      - a [constr] referring to a lemma, wrapped in [Some].
      - the value [None]

  Returns:
    - [constr]: the provided lemma, or [dummy_lemma] in case the input was [None]. [dummy_lemma] simply states that [0=0].
*)
Ltac2 unwrap_optional_lemma (lemma: constr option) :=
  match lemma with
    | None => constr:(I)
    | Some y => y
  end.