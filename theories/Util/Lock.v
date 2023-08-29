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


(* Code copied from Coq.ssr.ssreflect.
  Could not just import ssreflect because we have clashing notation. *)


Lemma master_key : unit. Proof. exact tt. Qed.

Definition locked {A} := let 'tt := master_key in fun x : A => x.

Definition lock A (x : A) : x = locked x :=
  (fun _evar_0_ : (fun u : unit => x = (let 'tt := u in fun x0 : A => x0) x) tt
  =>
  match master_key as u
    return ((fun u0 : unit => x = (let 'tt := u0 in fun x0 : A => x0) x) u)
  with
  | tt => _evar_0_
  end) eq_refl.
 
