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
(* Require Import Util.Goals. *)
(* Require Import Util.Hypothesis. *)
Require Import Waterprove.

Require Import Util.Init.
Local Ltac2 get_type (x: constr) : constr := eval unfold type_of in (type_of $x).

Ltac2 Type exn ::= [ BySinceError(message) ].

Local Ltac2 check_if_not_reference (x : constr) :=
  let type_x := get_type x in
  match check_constr_equal type_x constr:(Prop) with
  | true => ()
  | false => 
    match check_constr_equal type_x constr:(Set) with
    | true => ()
    | false => 
      match check_constr_equal type_x constr:(Type) with
      | true => ()
      | false => Control.zero (BySinceError (concat_list
        [of_string "Cannot use reference "; of_constr x; of_string " with 'Since ...'.";
        of_string " Try 'By "; of_constr x; of_string " ...' instead."]))
      end
    end
  end.

Local Ltac2 check_if_not_statement (x : constr) :=
  let err_msg := concat_list
    [of_string "Cannot use statement "; of_constr x; of_string " with 'By ...'.";
      of_string " Try 'Since "; of_constr x; of_string " ...' instead."]
  in
  let type_x := get_type x in
  match check_constr_equal type_x constr:(Prop) with
  | true => Control.zero (BySinceError err_msg)
  | false => 
    match check_constr_equal type_x constr:(Set) with
    | true => Control.zero (BySinceError err_msg)
    | false => 
      match check_constr_equal type_x constr:(Type) with
      | true => Control.zero (BySinceError err_msg)
      | false => ()
      end
    end
  end.


(** Attempts to prove [claimed_cause] with minimal automation, 
  and then executes [by_tactic] with the proof of [claimed_cause] 
  as an argument. 
  Expects that [by_tactic] can throw a [(Waterprove.)ByFailure] error,
  those errors are caught; the type of the constr-parameter of the [ByFailure] error
  is used in a new error that is thrown. It is expected that the constr-parameter
  is the proof which was passed into the [by_tactic], so its type is [claimed_cause].
*)

Ltac2 since_framework (by_tactic : constr -> unit) (claimed_cause : constr) :=
  (* first, check if [claimed_cause] is a statement. *)
  match Control.case (fun () => 
    check_if_not_reference claimed_cause)
  with 
  | Err exn => Control.zero exn
  | Val _ => ()
  end;
  
  let id_cause := Fresh.in_goal @_temp in
  (* attempt to prove [claimed_cause]*)
  match Control.case (fun () =>
    assert $claimed_cause as $id_cause by
      (waterprove 0 true [] Shorten))
  with
  | Err exn => 
    Control.zero (AutomationFailure (concat_list 
    [of_string "State that "; of_constr claimed_cause; of_string " holds";
    of_string " before using it in 'Since "; of_constr claimed_cause;
    of_string " ...'."]))
  | Val _ => 
    (* use proof of [claimed_cause] in [by_tactic] *)
    let cause := Control.hyp id_cause in
    match Control.case (fun () =>
      by_tactic cause)
    with
    | Val _ => clear $id_cause
    | Err exn => 
      match exn with
      | ByFailure h => 
        let type_h := (get_type h) in
        clear $id_cause;
        Control.zero (AutomationFailure (concat_list
        [of_string "Could not verify this follows from "; of_constr type_h; of_string "."]))
      | _ => clear $id_cause; Control.zero exn
      end
    end
  end.

(** Wrapper for the main functionality of 'By ...'-tactics, 
  such that the main fucntionality can be reused in 'Since ...'-tactics.

  Checks whether [xtr_lemma] is not a statement (i.e. not a Prop/Set/Type) and
  catches [(Waterprove.)ByFailure] errors to turn them into user-readable errors. *)
Ltac2 wrapper_core_by_tactic (by_tactic : constr -> unit) (xtr_lemma : constr) :=
  check_if_not_statement xtr_lemma;
  match Control.case (fun () => by_tactic xtr_lemma) with
  | Val _ => ()
  | Err exn => 
    match exn with
    | ByFailure h => Control.zero (AutomationFailure (concat_list
      [of_string "Could not verify this follows from "; of_constr h; of_string "."]))
    | _ => Control.zero exn
    end
  end.