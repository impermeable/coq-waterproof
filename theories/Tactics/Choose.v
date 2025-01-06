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

Require Import Util.Constr.
Require Import Util.Binders.
Require Import Util.Goals.
Require Import Util.MessagesToUser.
Require Import Util.Evars.

Require Import Tactics.BothStatements.

Require Import Notations.Sets.

Local Ltac2 concat_list (ls : message list) : message :=
  List.fold_right concat ls (of_string "").

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
  let sealed := lazy_match! (Control.goal ()) with
    | seal _ _ => unfold seal at 1; true
    | _ => false
    end in
  lazy_match! goal with
    | [ |- ex ?a] =>
      check_binder_warn a s true;
      pose ($s := $t);
      unfold subset_type in $s;
      let v := Control.hyp s in
      let w := Fresh.fresh (Fresh.Free.of_goal ()) @_defeq in
      match Constr.has_evar t with
      | true =>
        rename_blank_evars_in_term (Ident.to_string s) t;
        warn (concat_list [of_string "Please come back later to make a definitive choice for "; of_ident s; of_string "."; fnl ();
        of_string "For now you can use that "; of_constr constr:($v = $t); of_string "."]);
        assert_fix_earlier_warning ()
      | _ => ()
      end;
      exists $v;
      assert ($w : $v = $t) by reflexivity

    | [ |- _ ] => throw (of_string "`Choose` can only be applied to 'exists' goals.")
  end;
  if sealed then
    split;
    Control.focus 1 1 (fun () => unfold ge_op, R_ge_type, nat_ge_type,
      gt_op, R_gt_type, nat_gt_type, lt_op, R_lt_type, nat_lt_type,
      le_op, R_le_type, nat_le_type; apply VerifyGoal.unwrap);
    Control.focus 2 2 (fun () => apply StateGoal.unwrap)
  else ().

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
  let sealed := lazy_match! (Control.goal ()) with
  | seal _ _ => unfold seal at 1; true
  | _ => false
  end in
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
        assert_fix_earlier_warning ();
        eexists $t
      |  false => exists $t
      end
  | [ |- _ ] => throw (of_string "`Choose` can only be applied to 'exists' goals.")
  end;
  if sealed then
    split;
    Control.focus 1 1 (fun () => unfold ge_op, R_ge_type, nat_ge_type,
      gt_op, R_gt_type, nat_gt_type, lt_op, R_lt_type, nat_lt_type,
      le_op, R_le_type, nat_le_type; apply VerifyGoal.unwrap);
    Control.focus 2 2 (fun () => apply StateGoal.unwrap)
  else ().

Ltac2 Notation "Choose" s(opt(seq(ident, ":="))) t(open_constr) :=
  panic_if_goal_wrapped ();
  match s with
    | None => choose_variable_in_exists_no_renaming t
    | Some s => choose_variable_in_exists_goal_with_renaming s t
  end.
