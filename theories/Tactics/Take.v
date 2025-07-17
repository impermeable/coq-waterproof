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
  List.fold_right concat ls (of_string "").

Require Import Util.Binders.
Require Import Util.Constr.
Require Import Util.Goals.
Require Import Util.Hypothesis.
Require Import Util.MessagesToUser.

Require Import Stdlib.Sets.Ensembles.
Require Import Notations.Sets.

Local Ltac2 too_many_of_type_message (t : constr) :=
  concat_list [of_string "Tried to introduce too many variables of type ";
    of_constr t; of_string "."].

Local Ltac2 could_not_introduce_no_forall_message (id : ident) :=
  concat_list [of_string "Could not introduce "; of_ident id;
    of_string ". There is no variable to introduce at this point."].

Local Ltac2 expected_implication_message (id : ident) :=
  concat_list [of_string "Expected an implication after introducing ";
    of_ident id; of_string "."].

Local Ltac2 expected_of_type_instead_of_message (e : constr) (t : constr) :=
  concat_list [of_string "Expected variable of type "; of_constr e;
    of_string " instead of "; of_constr t; of_string "."].

Local Ltac2 expected_different_condition_message (e : constr) (expected : constr) :=
  concat_list [of_string "The condition " ; of_constr e; of_string " does not correspond to the expected condition "; of_constr expected].

Ltac2 Type TakeKind :=
  [TakeCol | TakeEl | TakeGt | TakeGe | TakeLt | TakeLe | TakeNone ].

Ltac2 string_to_take_kind (s : string) :=
  if String.equal s ":" then
    TakeCol
  else if String.equal s "∈" then
    TakeEl
  else if String.equal s ">" then
    TakeGt
  else if String.equal s "≥" then
    TakeGe
  else if String.equal s "<" then
    TakeLt
  else if String.equal s "≤" then
    TakeLe
  else
    (throw (of_string "Unknown symbol encountered after Take"); TakeCol).

Local Ltac2 get_take_kind (option_tuple : unit option * 'a option * 'b option * 'c option* 'd option * 'e option) :=
  let (col_opt, el_opt, gt_opt, ge_opt, lt_opt, le_opt) := option_tuple in
  let final_list := List.concat [
    (match col_opt with | Some _ => [TakeCol] | None => [] end);
    (match el_opt with | Some _ => [TakeEl] | None => [] end);
    (match gt_opt with | Some _ => [TakeGt] | None => [] end);
    (match ge_opt with | Some _ => [TakeGe] | None => [] end);
    (match lt_opt with | Some _ => [TakeLt] | None => [] end);
    (match le_opt with | Some _ => [TakeLe] | None => [] end)] in
  if Int.gt (List.length final_list) 1 then
    throw (of_string "Too many symbols provided to the 'Take' tactic. Use exactly one of: :, ∈, >, ≥, < , ≤"); TakeCol
    else
    match final_list with
    | [] => TakeNone
    | hd :: _ => hd
  end.

Local Ltac2 pred_from_take_kind (rhs : constr) (tk : TakeKind) :=
  match tk with
  | TakeCol => throw (Message.of_string "No assumption expected when using 'Take : '. Please report.");
      constr:(0)
  | TakeEl => constr:((∈ $rhs)%pfs)
  | TakeGt => constr:((> $rhs)%pfs)
  | TakeGe => constr:((≥ $rhs)%pfs)
  | TakeLt => constr:((< $rhs)%pfs)
  | TakeLe => constr:((≤ $rhs)%pfs)
  | TakeNone => rhs
  end.

Local Ltac2 intro_with_assum (id : ident) (rhs : constr) (tk : TakeKind) :=
  intro $id;
  unfold subset_type in $id;
  let id_c := Control.hyp id in
  let pred := pred_from_take_kind rhs tk in
  lazy_match! (Control.goal ()) with
  | (?cond -> _) => (* FIXME: this check should be more strict *)
    if check_constr_equal constr:($pred $id_c) cond then
      let w := Fresh.fresh (Fresh.Free.of_goal ()) @_H in
      intro $w;
      unfold ge_op, nat_ge_type, R_ge_type,
        gt_op, nat_gt_type, R_gt_type,
        lt_op, nat_lt_type, R_lt_type,
        le_op, nat_le_type, R_le_type in $w
    else
      throw (expected_different_condition_message constr:($pred $id_c) cond)
  | _ => throw (expected_implication_message id)
  end.


(**
  Introduces a variable.

    Arguments:
        - [id : ident ]: variable to introduce.
        - [rhs : constr]: the right-hand-side in the take-command for [id].
    Does:
        - Introduces the variable [id].
    Raises fatal exceptions:
        - If the current goal does not require the introduction
          of a variable of type [type], including coercions of [type].
*)
Local Ltac2 intro_ident (id : ident) (rhs : constr) (tk : TakeKind) :=
  let _ := lazy_match! Control.goal () with
    | seal _ _ => unfold seal at 1; true
    | _ => false
    end in
  let current_goal := Control.goal () in
  match Constr.Unsafe.kind (current_goal) with
  | Constr.Unsafe.Prod _ _ =>
      (* Check whether the expected binder name was provided. *)
      check_binder_warn current_goal id true
  | _ => throw (could_not_introduce_no_forall_message id)
  end;
  match tk with
  | TakeCol =>
    let type := rhs in
    lazy_match! (Control.goal ()) with
      | (forall _ : ?u, _) =>
        if check_constr_equal u (get_coerced_type type) then
          intro $id;
          unfold subset_type in $id
        else throw (too_many_of_type_message type)
      | _ => throw (could_not_introduce_no_forall_message id)
      end
  | TakeEl =>
    let type := rhs in
    intro $id;
    unfold subset_type in $id;
    let id_c := Control.hyp id in
    lazy_match! (Control.goal ()) with
    | (?v ∈ ?set_in_cond -> _) =>
      let possibly_coerced_type :=
        lazy_match! Constr.type type with
        | Ensemble _ => type
        | _ -> Prop => type
        | _ => get_coerced_type type
        end in
      let possibly_coerced_set :=
        lazy_match! set_in_cond with
        | conv ?typ => typ
        | _ => set_in_cond
        end in
      if Bool.and (Constr.equal v id_c)
        (check_constr_equal possibly_coerced_set possibly_coerced_type) then
        let w := Fresh.fresh (Fresh.Free.of_goal ()) @_H in
        intro $w (* TODO: could remove when this is trivial... *)
      else
        throw (expected_different_condition_message constr:($v ∈ $set_in_cond)
          constr:($id_c ∈ $rhs))
    | _ => throw (expected_implication_message id)
    end
  | _ => intro_with_assum id rhs tk
  end.

(**
  Introduces a list of variables of single type.

  Arguments:
    - [pair : (ident list * constr)]: list of variables paired with their type.

  Does:
    - Introduces the variables in [pair].

  Raises fatal exceptions:
    - If the current goal does not require the introduction of a variable of type [type], including coercions of [type].
*)
Local Ltac2 intro_per_type (pair : (ident list * unit option * 'a option * 'b option * 'c option * 'd option * 'e option * constr)) :=
  let (ids, col_opt, in_opt, gt_opt, ge_opt, lt_opt, le_opt, type) := pair in
  let take_kind := get_take_kind (col_opt, in_opt, gt_opt, ge_opt, lt_opt, le_opt) in
  lazy_match! goal with
    | [ |- seal (fun _ => forall _ : ?u, _) _ ] =>
      let sort_u := get_value_of_hyp u in
      match check_constr_equal sort_u constr:(Prop) with
        | false =>
          List.iter (fun id => intro_ident id type take_kind) ids
        | true  => throw (of_string "Tried to introduce too many variables.")
      end
    | [ |- forall _ : ?u, _] =>
      (* Check whether [u] is not a proposition. *)
      let sort_u := get_value_of_hyp u in
      match check_constr_equal sort_u constr:(Prop) with
        | false =>
          List.iter (fun id => intro_ident id type take_kind) ids
        | true  => throw (of_string "Tried to introduce too many variables.")
      end
    | [ |- _ ] => throw (of_string "Tried to introduce too many variables.")
  end.

(**
  Checks whether variables need to be introduced, attempts to introduce a list of variables of certain types.
*)
Local Ltac2 take (x : (ident list * unit option * 'a option * 'b option * 'c option * 'd option * 'e option * constr) list) :=
  lazy_match! goal with
    | [ |- seal (fun _ => forall _ : ?u, _) _ ] =>
      (* Check whether [u] is not a proposition. *)
      let sort_u := get_value_of_hyp u in
      match check_constr_equal sort_u constr:(Prop) with
        | false => List.iter intro_per_type x
        | true  => throw (of_string "`Take ...` cannot be used to prove an implication (⇨). Use `Assume that ...` instead.")
      end
    | [ |- forall _ : ?u, _] =>
      (* Check whether [u] is not a proposition. *)
      let sort_u := get_value_of_hyp u in
      match check_constr_equal sort_u constr:(Prop) with
        | false => List.iter intro_per_type x
        | true  => throw (of_string "`Take ...` cannot be used to prove an implication (⇨). Use `Assume that ...` instead.")
      end
    | [ |- _ ] => throw (of_string "`Take ...` can only be used to prove a `for all`-statement (∀) or to construct a map (→).")
  end.

Ltac2 Notation "Take" x(list1(seq(list1(ident, ","),
  opt (":"), opt("∈"), opt(">"), opt("≥"), opt("<"), opt("≤"), lconstr), "and")) :=
  panic_if_goal_wrapped ();
  take x.
