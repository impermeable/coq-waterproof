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

From Ltac2 Require Import Ltac2.
From Waterproof Require Import Waterproof Util.EnsureProp.

Lemma test : 0 = 0.
Proof.
  Ltac2 Eval ensure_prop constr:(0 = 0). (* Prop *)
  Ltac2 Eval ensure_prop constr:(true). (* bool -> gets converted to is_true true *)
  Ltac2 Eval ensure_prop constr:(true = true). (* Prop *) 
  Fail Ltac2 Eval ensure_prop constr:(0). (* Fail, as this is of type nat *)
Abort.