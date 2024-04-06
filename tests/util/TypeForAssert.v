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
From Waterproof Require Import Waterproof. 
From Waterproof Require Import Util.TypeForAssert.

Section assert_tests.

Parameter setS : Set.
Parameter s : setS.

Lemma test : 0 = 0.
Proof.
  (* Let binding gets rid of the output messages *)
  let res := correct_type_for_assert constr:(0 = 0) in (). (* Prop *)
  let res := correct_type_for_assert constr:(true) in (). (* bool -> gets converted to is_true true *)
  let res := correct_type_for_assert constr:(true = true) in (). (* Prop *) 
  let res := correct_type_for_assert constr:(setS) in ().
  Fail Ltac2 Eval correct_type_for_assert constr:(0). (* Fail, as this is of type nat *)
  (* Fail let test := correct_type_for_assert constr:(0) in ().  *)
  Fail Ltac2 Eval correct_type_for_assert constr:(s). (* Fails as this term has type setS, which we do not recognise *)
Abort.

End assert_tests.