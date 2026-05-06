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
