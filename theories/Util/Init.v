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

(** * type_of

  Gallina function mapping a term to its type.

  Arguments:
    - [T:type], any type
    - [x:T], a term of a generic type T.
  Returns:
    - [T], the type of x.
*)
Definition type_of {T : Type} (x : T) := T.