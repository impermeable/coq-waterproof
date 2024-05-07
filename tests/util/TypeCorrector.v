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
From Waterproof Require Import Util.MessagesToUser.
From Waterproof Require Import Util.TypeCorrector.

Section assert_tests.

Parameter setS : Set.
Parameter s : setS.

Parameter typeT : Type.
Parameter t : typeT.

Lemma test : 0 = 0.
Proof.
  (* The statement (0 = 0) has type Prop so nothing should happen and resulting type should be Prop. *)
  let res := correct_type_by_wrapping constr:(0 = 0) in (
    match! Constr.type res with 
    | Prop => ()
    | _ => throw ( Message.of_string "Expected resulting type to be Prop." )
    end;
    let expected_constr := constr:(0 = 0) in
    if Constr.equal res expected_constr 
      then () 
      else throw ( Message.of_string "Expected resulting term to be '0 = 0'." )
  ).

  (* The statement 'true' has type bool so this should get wrapped in 'is_true (true)' which has type Prop. *)
  let res := correct_type_by_wrapping constr:(true) in (
    match! Constr.type res with 
    | Prop => ()
    | _ => throw ( Message.of_string "Expected resulting type to be Prop." )
    end;
    let expected_constr := constr:(is_true true) in
    if Constr.equal res expected_constr 
      then () 
      else throw ( Message.of_string "Expected resulting term to be 'is_true true'." )
  ).

  (* The statement 'true = true' has type Prop so nothing should happen and resulting type should be Prop. *)
  let res := correct_type_by_wrapping constr:(true = true) in (
    match! Constr.type res with
    | Prop => ()
    | _ => throw ( Message.of_string "Expected resulting type to be Prop." )
    end;
    let expected_constr := constr:(true = true) in
    if Constr.equal res expected_constr 
      then () 
      else throw ( Message.of_string "Expected resulting term to be 'true = true'." )
  ).

  (* setS has type Set which should not change *)
  let res := correct_type_by_wrapping constr:(setS) in (
    match! Constr.type res with
    | Set => ()
    | _ => throw ( Message.of_string "Expected resulting type to be Set." )
    end;
    let expected_constr := constr:(setS) in
    if Constr.equal res expected_constr 
      then () 
      else throw ( Message.of_string "Expected resulting term to be 'setS'." )
  ).

  (* typeT has type Type which should not change *)
  let res := correct_type_by_wrapping constr:(typeT) in (
    match! Constr.type res with
    | Type => ()
    | _ => throw ( Message.of_string "Expected resulting type to be Type." )
    end;
    let expected_constr := constr:(typeT) in
    if Constr.equal res expected_constr 
      then () 
      else throw ( Message.of_string "Expected resulting term to be 'typeT'." )
  ).

  (* 0 has type nat and this should fail *)
  Fail Ltac2 Eval correct_type_by_wrapping constr:(0).

  (* s has type setS and this should fail *)
  Fail Ltac2 Eval correct_type_by_wrapping constr:(s).

  (* t has type typeT and this should fail *)
  Fail Ltac2 Eval correct_type_by_wrapping constr:(t).
Abort.

End assert_tests.