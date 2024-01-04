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

Require Import Util.Goals.
Require Import Util.MessagesToUser.

(* Ltac2 Type exn ::= [ ChooseError(string) ]. *)


(** * Choose *)

(**
    
  Instantiate a variable in an [exists] [goal], according to a given [constr], and also renames the [constr].

  Arguments:
    - [s: ident], an [ident] for naming an idefined [constr]/variable.
    - [t: constr], the requirted [constr] that needs to be instantiated.

  Does:
    - instantiates the [constr] [t] under the name [s].

  Raises fatal exceptions:
    - If the [goal] is not an [exists] [goal].
*)
Ltac2 choose_variable_in_exists_goal_with_renaming (s:ident) (t:constr) :=
  lazy_match! goal with
    | [ |- exists _ : _, _] =>
      pose ($s := $t);
      let v := Control.hyp s in
      let w := Fresh.fresh (Fresh.Free.of_goal ()) @_defeq in
      exists $v;
      assert ($w : $v = $t) by reflexivity
    | [ |- _ ] => throw (of_string "`Choose` can only be applied to 'exists' goals.")
  end.



(**
  Instantiate a variable in an [exists] [goal], according to a given [constr], without renaming said [constr].

  Arguments:
    - [t: constr], the requirted [constr] that needs to be instantiated.

  Does:
    - instantiates the [constr] [t] under the same name.

  Raises fatal exceptions:
    - If the [goal] is not an [exists] [goal].
*)
Ltac2 choose_variable_in_exists_no_renaming (t:constr) :=
    lazy_match! goal with
        | [ |- exists _ : _, _] => exists $t
        | [ |- _ ] => throw (of_string "`Choose` can only be applied to 'exists' goals.")
    end.

Ltac2 Notation "Choose" s(opt(seq(ident, ":="))) t(constr) :=
  panic_if_goal_wrapped ();
  match s with 
    | None => choose_variable_in_exists_no_renaming t
    | Some s => choose_variable_in_exists_goal_with_renaming s t
  end.

