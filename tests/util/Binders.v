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

Require Import Waterproof.Util.Binders.
Require Import Waterproof.Notations.Sets.
Require Import Ltac2.Message.
Require Import Waterproof.Util.MessagesToUser.
Require Import Waterproof.Util.Assertions.

Open Scope subset_scope.

Local Ltac2 concat_list (ls : message list) : message :=
  List.fold_right concat (of_string "") ls.

Waterproof Enable Redirect Feedback.

(** Test 1 : warn on wrong binder *)
Goal forall x : nat, x = 0.
Proof.
assert_feedback_with_string
  (fun () => check_binder_warn (Control.goal ()) @y false) Warning
"Expected variable name x instead of y.".
Abort.

(** Test 2 : Test that binder can get renamed
    by change_binder_name_under_seal function *)
Goal False.
Proof.
let new_stmt :=
  (change_binder_name_under_seal
  constr:(∀ k ∈ nat, k = 3) @l) in
let unsealed_stmt :=
  eval unfold seal at 1 in $new_stmt in
match check_binder_name unsealed_stmt @l false with
| None => ()
| Some x => Control.zero (TestFailedError
  (concat_list
   [of_string "expected binder name ";
    of_ident @l;
    of_string " instead of ";
    of_ident x]))
end.
Abort.
