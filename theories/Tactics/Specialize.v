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

Require Import Util.Init.
Require Import Util.Goals.
Require Import Util.MessagesToUser.


(**
  Specializes a hypothesis that starts with a for-all statement.
    
  Arguments:
    - [s : ident], name of the variable to choose
    - [choice : constr], choice for the variable
    - [in_hyp : ident], name of the hypothesis to specialize.

  Raises fatal exceptions:
    - If the hypothesis [in_hyp] does not start with a for-all statement.
*)
Local Ltac2 wp_specialize (s:ident) (choice:constr) (in_hyp:ident) :=
  let h := Control.hyp in_hyp in
  let statement := eval unfold type_of in (type_of $h) in
  let specialized_statement := eval unfold type_of in (type_of ($h $choice)) in
  lazy_match! statement with
    | forall _ : _, _ =>
      let w := Fresh.fresh (Fresh.Free.of_goal ()) @_spec in
      (* Check whether it is really a specialization *)
      (assert ($w : $specialized_statement) by exact ($h $choice));
      (* Remove the hypothesis again *)
      Control.enter (fun () => clear $w);
      (* Wrap the goal *)
      (* Control.enter (fun () => apply (StateHyp.unwrap $specialized_statement)) *)apply (StateHyp.unwrap $specialized_statement)
    | _ => throw (of_string "`Choose ... in (*)` only works if (*) starts with a for-all quantifier.")
  end.

(**
  Specializes a hypothesis that starts with a for-all statement.
    
  Arguments:
    - [s : ident], name of the variable to choose
    - [choice : constr], choice for the variable
    - [in_hyp : ident], name of the hypothesis to specialize.

  Raises fatal exceptions:
    - If the hypothesis [in_hyp] does not start with a for-all statement.
*)
Ltac2 Notation "Pick" s(ident) ":=" choice(constr) "in" in_hyp(ident) :=
  wp_specialize s choice in_hyp.
