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
From Ltac2 Require Import Message.
Require Import Notations.Sets.
Require Import Util.MessagesToUser.

Local Ltac2 concat_list (ls : message list) : message :=
  List.fold_right concat ls (of_string "").


(**
  Check whether the provided variable name [candidate_name]
  corresponds to the name of the binder [b]

  Arguments:
  - [b : binder], the binder to check.
  - [candidate_name : ident], the candidate name for the binder
  - [guess_name : bool], whether to use a guess for the visually renamed binder,
    or to go with the exact binder name.

  Returns:
  - [ident option] - None if the binder name agrees, otherwise the expected/guessed binder name
*)
Local Ltac2 check_binder (b : binder) (candidate_name : ident) (guess_name : bool)
  : ident option :=
  match Constr.Binder.name b with
| None => None (* TODO: is it true that we want to do nothing here?,
                i.e. in the case of anonymous binders. *)
| Some binder_name =>
    (* If a variable already exists, the binder gets renamed visually, but
    the binder name internally remains the same.
    This gives confusing behavior. To go around this,
    we try to guess what the binder got renamed into by introducing a fresh
    ident based on the binder name. *)
    let fresh_binder_name :=
      if guess_name then
        Fresh.fresh (Fresh.Free.of_goal () ) binder_name
      else binder_name in
    if Ident.equal fresh_binder_name candidate_name then
      None
    else
      Some fresh_binder_name
 end.

(**
  Check whether the provided variable name [candidate_name]
  corresponds to the first expected binder name in [expr].

  Arguments:
  - [expr: constr], the expression in which a binder occurs of which the
    name should be checked.
  - [candidate_name : ident], the candidate name for the binder
  - [guess_name : bool], whether to use a guess for the visually renamed binder,
    or to go with the exact binder name.

  Returns:
  - [ident option] - None if the binder name agrees, otherwise the expected/guessed binder name
*)
Ltac2 check_binder_name (expr : constr) (candidate_name : ident) (guess_name : bool) :
  ident option :=
  match (Constr.Unsafe.kind expr) with
  | Constr.Unsafe.Lambda b _ => check_binder b candidate_name guess_name
  | Constr.Unsafe.Prod b _=> check_binder b candidate_name guess_name
  | _ => None
  end.

(**
  Check whether the provided variable name [candidate_name]
  corresponds to the first expected binder name in [expr].

  Warns in case of a mismatch.

  Arguments:
  - [expr: constr], the expression in which a binder occurs of which the
    name should be checked.
  - [candidate_name : ident], the candidate name for the binder
  - [exact_correspondence : bool], whether the binder name should correspond exactly (argument true) or whether
    the visually displayed binder name is guessed
*)
Ltac2 check_binder_warn (expr : constr) (candidate_name) (exact_correspondence : bool) : unit :=
  match check_binder_name expr candidate_name exact_correspondence with
  | None => ()
  | Some fresh_binder_name =>
      warn (concat_list [of_string "Expected variable name ";  of_ident fresh_binder_name;
        of_string " instead of "; of_ident candidate_name;
        of_string "."])
  end.

(**
If the constr [c] is of sealed product type (the types
that we use for the custom waterproof forall notation),
then return a constr in which the binder name associated
to the product is changed to [id]

Arguments:
  - [c : constr] The expression in which the binder
    name should be changed
  - [id : constr] The new binder name

Returns:
  - [constr] The new expression with the new binder name
*)
Ltac2 change_binder_name_under_seal (c : constr) (id : ident) :=
  (* Introduced as an inline function because we use it in a situation
     where the produced term is not yet safe in the current environemnt.
     The check for safety happens later in the function
     [change_binder_name_under_seal] *)
  let change_binder_name (c : constr) (id : ident) :=
    match Constr.Unsafe.kind c with
    | Constr.Unsafe.Prod a b =>
        let bi := Constr.Binder.make (Some id) (Constr.Binder.type a) in
        Constr.Unsafe.make (Constr.Unsafe.Prod bi b)
    | _ => c
    end in
  lazy_match! c with
  | seal ?f ?d =>
      let new_f :=
        match Constr.Unsafe.kind f with
        | Constr.Unsafe.Lambda a b =>
          let stmt := change_binder_name b id in
          Constr.Unsafe.make (Constr.Unsafe.Lambda a stmt)
        | _ => f
        end in
      match Constr.Unsafe.check new_f with
      | Val x => constr:(seal $new_f $d)
      | Err exn => c
      end
  | _ => c
  end.
