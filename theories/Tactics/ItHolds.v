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

Require Import Util.Constr.
Require Import Util.Goals.
Require Import Util.Hypothesis.
Require Import Util.Init.
Require Import Waterprove.


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


(** Attempts to assert that [claim] holds, if succesful [claim] is added to the local
  hypotheses. If [label] is specified [claim] is given [label] as its identifier, otherwise an
  identifier starting with '_H' is generated. *)
Local Ltac2 wp_assert (claim : constr) (label : ident option) :=
  let err_msg := concat_list
    [of_string "Could not verify that "; of_constr claim; of_string "."] in
  let id := 
    match label with 
    | None => Fresh.in_goal @_H
    | Some label => try_out_label label; label
    end
  in
  match Control.case (fun () =>
    assert $claim as $id by 
      (waterprove 5 true [] Main))
  with
  | Val _ => ()
  | Err exn => Control.zero (AutomationFailure err_msg)
  end.


(** Attempts to assert that [claim] holds, if succesful [claim] is added to the local
  hypotheses. If [label] is specified [claim] is given [label] as its identifier, otherwise an
  identifier starting with '_H' is generated.
  [xtr_lemma] has to be used in the proof that [claim] holds, otherwise an [AutomationFailure]
  error is thrown.
  *)
Local Ltac2 wp_assert_by (claim : constr) (label : ident option) (xtr_lemma : constr) :=
  let err_msg := concat_list
    [of_string "Could not verify that "; of_constr claim; of_string "."] in
  let id := 
    match label with 
    | None => Fresh.in_goal @_H
    | Some label => try_out_label label; label
    end
  in
  match Control.case (fun () =>
    assert $claim as $id by 
      (rwaterprove 5 true [fun() => xtr_lemma] Main [xtr_lemma] []))
  with
  | Val _ => ()
  | Err exn => (* failed, if due to restricition, give feedback *)
    (* check if it would work without lemma *)
    match Control.case (fun () =>
    assert $claim as $id by 
        (waterprove 5 true [] Main))
    with
    | Err exn => Control.zero (AutomationFailure err_msg)
    | Val _ =>
      (* problem is the extra lemma: it is not used for proof equivalence *)
      Control.zero (AutomationFailure ( concat_list 
        [of_string "Could not verify this follows from "; of_constr xtr_lemma;
         of_string "."]))
    end
  end.



(**
  Attempts to assert a claim and proves it automatically using a specified lemma, 
  this lemma has to be used.

  Arguments:
    - [xtr_lemma: constr], reference to a lemma used to prove the claim (via [rwaterprove]).
    - [label: ident option], optional name for the claim. 
        If the proof succeeds, it will become a hypothesis (bearing [label] as name).
    - [claim: constr], the actual content of the claim to prove.

    Raises exception:
    - [AutomationFailure], if [rwaterprove] fails to prove the claim using the specified lemma.
    - [[label] is already used], if there is already another hypothesis with identifier [label].
*)
Ltac2 Notation "By" xtr_lemma(constr) "it" "holds" "that" claim(constr) label(opt(seq("(", ident, ")"))) :=
  panic_if_goal_wrapped ();
  wp_assert_by claim label xtr_lemma.
    
    
(** * It holds that ... (...)
  Attempts to assert a claim and proves it automatically.

  Arguments:
    - [label: ident option], optional name for the claim. 
        If the proof succeeds, it will become a hypothesis (bearing [label] as name).
    - [claim: constr], the actual content of the claim to prove.

    Raises exception:
    - [AutomationFailure], if [rwaterprove] fails to prove the claim using the specified lemma.
    - [[label] is already used], if there is already another hypothesis with identifier [label].
*)
Ltac2 Notation "It" "holds" "that" claim(constr) label(opt(seq("(", ident, ")")))  :=
  panic_if_goal_wrapped ();
  wp_assert claim label.