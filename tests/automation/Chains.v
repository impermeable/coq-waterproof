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

Require Import Waterproof.Waterproof.
Require Import Waterproof.Notations.

Require Import Waterproof.Waterprove.


(** Tests whether the error points out which specific (in)equality in the chain does not hold. *)
Local Parameter X : Type.
Local Parameter a b c : X.

(* Test 1: first equality does not hold. *)
Goal (& a = b = c).
Proof.
  Fail waterprove 5 true Main. (* Expected: unable to find proof (a = b) *)
Abort.

(* Test 2: last equality does not hold.  *)
Goal (a = b) -> (& a = b = c).
Proof.
  intro p.
  Fail waterprove 5 true Main. (* Expected: unable to find proof (b = c) *)
Abort.

(** Test restricted automation. *)
Variable P : Prop.
Variable h : P -> a = b.
#[local] Hint Extern 1 => symmetry : core.

(* Test 3: fails without extra lemma. *)
Goal P -> (& a = b = b = b = b = a).
Proof.
  intro H.
  Fail waterprove 5 true Main.
Abort.

(* Test 4: extra lemma has to be used in first equality. *)
Goal P -> (& a = b = b = b = b = b).
Proof.
  intro H.
  rwaterprove 5 true Main constr:(h).
Abort.

(* Test 5: extra lemma has to be used in last equality. *)
Goal P -> (& b = b = b = b = b = a).
Proof.
  intro H.
  rwaterprove 5 true Main constr:(h).
Abort.

(* Test 6: extra lemma has to be used in 2nd and 2nd-to-last equality. *)
Goal P -> (& b = b = a = b = b = a = a).
Proof.
  intro H.
  rwaterprove 5 true Main constr:(h).
Abort.

(* Test 7: Fails if extra lemma is never used. *)
Goal P -> (P -> b = c) -> (& b = b = c = b = b = c = c).
Proof.
  intros H1 H2.
  Fail rwaterprove 5 true Main constr:(h).
Abort.