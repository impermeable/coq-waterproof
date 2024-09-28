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

Require Import Util.Binders.
Require Import Util.Goals.
Require Import Util.MessagesToUser.
Require Import Util.Evars.

Require Import Tactics.BothStatements.

Require Import Notations.Sets.

Local Ltac2 concat_list (ls : message list) : message :=
  List.fold_right concat (of_string "") ls.

(* Ltac2 Type exn ::= [ ChooseError(string) ]. *)

Local Ltac2 _binder_name_equal (name : ident) (b : binder) :=
  match Constr.Binder.name b with
  | None => false
  | Some binder_name => Ident.equal name binder_name
  end.

(** * Choose *)

(**

  Instantiate a variable in an [exists] [goal], according to a given [constr], and also renames the [constr]. The [constr] can contain blanks, which are filled in
  with freshly named evars, so that the user can refer to them later.

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
    | [ |- ex ?a] =>
      check_binder_name a s;
      set ($s := $t);
      let v := Control.hyp s in
      let w := Fresh.fresh (Fresh.Free.of_goal ()) @_defeq in
      match Constr.has_evar t with
      | true =>
        rename_blank_evars_in_term (Ident.to_string s) t;
        warn (concat_list [of_string "Please come back later to make a definitive choice for "; of_ident s; of_string "."; fnl ();
        of_string "For now you can use that "; of_constr constr:($v = $t); of_string "."])
      | _ => ()
      end;
      exists $v;
      assert ($w : $v = $t) by reflexivity

    | [ |- _ ] => throw (of_string "`Choose` can only be applied to 'exists' goals.")
  end;
  let v := Control.hyp s in
  lazy_match! goal with
  | [ |- (pred _ _) ?c /\ _] =>
    if Constr.equal c v then
      split;
      (* TODO: attempt to prove first statement automatically *)
      Control.enter (fun () => apply StateGoal.unwrap)
      else ()
  | [ |- _ ] => ()
  end.

(**
  Instantiate a variable in an [exists] [goal], according to a given [constr], without renaming said [constr]. The [constr] can contain blanks, which are filled in
  with freshly named evars, so that the user can refer to them later.

  Arguments:
    - [t: constr], the requirted [constr] that needs to be instantiated.

  Does:
    - instantiates the [constr] [t] under the same name.

  Raises fatal exceptions:
    - If the [goal] is not an [exists] [goal].
*)
Ltac2 choose_variable_in_exists_no_renaming (t:constr) :=
  lazy_match! goal with
  | [ |- ex ?a] =>
      (* Make a suggestion of the base name for renaming of blank evars *)
      let name :=
        match Constr.Unsafe.kind a with
        | Constr.Unsafe.Lambda b _ =>
          match Constr.Binder.name b with
          | Some x => Ident.to_string x
          | None => "x"
          end
        | _ => "x"
        end
      in
      match Constr.has_evar t with
      |  true =>
        rename_blank_evars_in_term name t;
        warn (concat_list [of_string "Please come back later to make a definite choice."]);
        eexists $t
      |  false => exists $t
      end
  | [ |- _ ] => throw (of_string "`Choose` can only be applied to 'exists' goals.")
  end.

Ltac2 Notation "Choose" s(opt(seq(ident, ":="))) t(open_constr) :=
  panic_if_goal_wrapped ();
  match s with
    | None => choose_variable_in_exists_no_renaming t
    | Some s => choose_variable_in_exists_goal_with_renaming s t
  end.
