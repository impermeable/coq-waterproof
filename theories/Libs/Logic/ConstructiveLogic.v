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

(** ClassicalEpsilon allows us to lift an uninformative or to an informative or. *)

Lemma make_sumbool_uninformative_1 : forall P Q : Prop, {P} + {Q} -> P \/ Q.
Proof.
intros P Q H.
destruct H.
- left.
  exact p.
- right.
  exact q.
Qed.

Lemma make_sumbool_uninformative_2 : forall P Q : Prop, {Q} + {P} -> P \/ Q.
Proof.
intros P Q H.
destruct H.
- right.
  exact q.
- left.
  exact p.
Qed.

Lemma make_sumtriad_uninformative_1 : forall P Q R: Prop, {P} + {Q} + {R} -> P \/ Q \/ R.
Proof.
intros P Q R H.
destruct H as [H1 | H2].
- destruct H1.
  * left.
    exact p.
  * right.
    left.
    exact q.
- right.
  right.
  exact H2.
Qed.

Lemma make_sumtriad_uninformative_2 : forall P Q R: Prop, {P} + {R} + {Q} -> P \/ Q \/ R.
Proof.
intros P Q R H.
destruct H as [H1 | r].
- destruct H1 as [p | q].
  * left.
    exact p.
  * right.
    right.
    exact q.
- right.
  left.
  exact r.
Qed.

Lemma make_sumtriad_uninformative_3 : forall P Q R: Prop, {Q} + {P} + {R} -> P \/ Q \/ R.
Proof.
intros P Q R H.
destruct H as [H1 | r].
- destruct H1.
  * right.
    left.
    exact q.
  * left.
    exact p.
- right.
  right.
  exact r.
Qed.

Lemma make_sumtriad_uninformative_4 : forall P Q R: Prop, {Q} + {R} + {P} -> P \/ Q \/ R.
Proof.
intros P Q R H.
destruct H as [H1 | p].
- destruct H1 as [q | r].
  * right.
    left.
    exact q.
  * right.
    right.
    exact r.
- left.
  exact p.
Qed.

Lemma make_sumtriad_uninformative_5 : forall P Q R: Prop, {R} + {P} + {Q} -> P \/ Q \/ R.
Proof.
intros P Q R H.
destruct H as [H1 | q].
- destruct H1 as [r | p].
  * right.
    right.
    exact r.
  * left.
    exact p.
- right.
  left.
  exact q.
Qed.

Lemma make_sumtriad_uninformative_6 : forall P Q R: Prop, {R} + {Q} + {P} -> P \/ Q \/ R.
Proof.
intros P Q R H.
destruct H as [H1 | p].
- destruct H1 as [r | q].
  * right.
    right.
    exact r.
  * right.
    left.
    exact q.
- left.
  exact p.
Qed.

