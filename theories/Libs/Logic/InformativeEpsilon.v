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

Require Import ClassicalEpsilon.

(** ClassicalEpsilon allows us to lift an uninformative or to an informative or. *)

Lemma informative_or_lift : forall P Q : Prop, P \/ Q -> {P} + {Q}.
Proof.
intros P Q.
assert ({P} + {~P}) as H by (apply excluded_middle_informative).
destruct H.
* intro.
  left.
  exact p.
* intros H.
  assert ({Q} + {~Q}) as H2 by (apply excluded_middle_informative).
  destruct H2.
  + right.
    exact q.
  + assert (~~Q).
    {
      destruct H.
      + contradiction.
      + intro H1.
        destruct H1.
        exact H.
    }
    contradiction.
Qed.
