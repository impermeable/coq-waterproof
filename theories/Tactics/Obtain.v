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
Require Import Ltac2.Message.
Local Ltac2 concat_list (ls : message list) : message :=
  List.fold_right concat (of_string "") ls.

Require Import Util.Init.
Local Ltac2 get_type (x: constr) : constr := eval unfold type_of in (type_of $x).

Require Import Util.Goals.
Require Import Util.MessagesToUser.

(** Tries to make the assertion [True] with label [label].
  Throws an error if this fails, i.e. if the label is already used
  for another one of the hypotheses.
  
  This check was separated out from the 'assert'-tactics below because the 
  '[label] is already used error' would otherwise be caught in
  the code meant to catch [AutomationFailure] errors. *)

Local Ltac2 try_out_label (label : ident) :=
  match Control.case (fun () => 
    assert True as $label by exact I)
  with
  | Err exn => Control.zero exn
  | Val _ => clear $label
  end.

(** Destructs the statement with label [og_label] into the variable named [var_label] 
  and the corresponding property. Copies statement [og_label] such that the statement 
  is preserved despite its destruction. 
  
  The original, not the copy, is destructed because with sigma types the goal
  or other hypotheses can depend on the specific instance of the original.*)  

Local Ltac2 copy_and_destruct (og_label : ident) (var_label : ident) :=
  let og_term := Control.hyp og_label in
  let og_type := get_type og_term in
  (* make temporary copy; destruct original; make new copy with original label. *)
  (* make temporary copy statement *)     
  let temp_id := Fresh.in_goal @_temp_copy in
  assert $og_type as $temp_id;
  Control.focus 1 1 (fun () => exact $og_term); 
    (* (above line) separate from 'assert' 
      as otherwise $copy_id could not be found..?*)
  (* destruct original *)
  let prop_label := Fresh.in_goal @_H in
  destruct $og_term as [$var_label $prop_label];
  (* make new copy with original label *)
  let temp_copy := Control.hyp temp_id in 
  assert $og_type as $og_label;
  Control.focus 1 1 (fun () => exact $temp_copy);
  (* remove temporary copy *)
  clear $temp_id.


(** *
  Attempts to obtain a variable from the previous statement.

  Arguments:
    - [var : ident], the name of the variable to be obtained.
  Does:
    - Destructs the previous statement into the variable [var] and its corresponding property.
    - Copies the previous statement into a new statement with the same identifier 
      to preserve the statement despite its destruction.

  Raises fatal exceptions:
    - If no statement to destruct or if the previous statement was not an
      existence statement or a sigma type.
*)

Ltac2 obtain_according_to_last (var : ident) :=
  lazy_match! goal with
  | [id_h : _ |- _ ] => 
    let h := Control.hyp id_h in
    let type_h := get_type h in
    lazy_match! type_h with
    | ex  ?pred => copy_and_destruct id_h var
    | sig ?pred => copy_and_destruct id_h var
    | _ => throw (of_string 
      "Previous statement is not of the form 'there exists ...'.")
    end
  | [ |- _] => throw (of_string 
    "No statement to obtain variable from.")
  end.

(** *
  Attempts to obtain a variable from a user-specified statement.

  Arguments:
    - [var : ident], the name of the variable to be obtained.
    - [hyp : ident], label of the statement the variable should be obtained from.
  Does:
    - Destructs the statement [hyp] into the variable [var] and its corresponding property.
    - Copies the statement [hyp] into a new statement with the same label [hyp]
      to preserve the statement despite its destruction.

  Raises exceptions:
    - [ObtainError], if no statement to destruct or if the previous statement was not an
      existence statement or a sigma type.
*)

Ltac2 obtain_according_to (var : ident) (hyp : ident) :=
  let h := Control.hyp hyp in
  let type_h := get_type h in
  lazy_match! type_h with
  | ex  ?pred => copy_and_destruct hyp var
  | sig ?pred => copy_and_destruct hyp var
  | _ => throw (concat_list 
    [of_string "Statement "; of_constr h; of_string " is not of the form 'there exists ...'."])
  end.

  
Ltac2 Notation "Obtain" "such" a(opt("a")) an(opt("an")) var(ident) :=
  panic_if_goal_wrapped ();
  try_out_label var;
  obtain_according_to_last var.

Ltac2 Notation "Obtain" var(ident) "according" "to" hyp(seq("(", ident, ")")):=
  panic_if_goal_wrapped ();
  try_out_label var;
  obtain_according_to var hyp.
