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

Require Import Waterproof.
Require Import Ltac2.Message.
Local Ltac2 concat_list (ls : message list) : message :=
  List.fold_right concat ls (of_string "").

Require Import Util.Binders.
Require Import Util.Constr.
Require Import Util.Init.
Require Import Util.Goals.
Require Import Util.MessagesToUser.
Require Import Util.Evars.
Require Import Notations.Sets.

(**
  Convert a (ident * constr) to a (Std.hypothesis * constr) list,
  by applying Std.NamedHyp to the first arguments of the pairs.
*)
Local Ltac2 _ident_to_hyp_list (ls : (ident * constr) list) : (Std.hypothesis * constr) list
 := List.map (fun (i, x) => (Std.NamedHyp i, x)) ls.

(**
  Get those names from a list of pairs of idents and choice
  for those idents, and selects those names where the choice
  has an evar.
*)
Local Ltac2 _names_evars (ls : (ident * constr) list) : ident list
 := List.map (fun (i, _) => i) (List.filter (fun (_, x) => Constr.has_evar x) ls).

(**
  Helper function to make a message of a list of idents,
  joining them together separated by commas.
*)
Local Ltac2 rec _of_idents (xs : ident list) : message
 := match List.rev(xs) with
    | t::[] => of_ident t
    | t::ls => concat_list [_of_idents (List.rev(ls)); of_string ", "; of_ident t]
    | [] => of_string ""  (* not used *)
    end.

(**
  Checks whether a list is empty.
  TODO: the standard library has this function in a later version, we should use it in later versions.
*)
Local Ltac2 is_empty (ls : 'a list) : bool
 := match ls with
    | _::_ => false
    | [] => true
    end.

(**
  Get all product binders at the beginning of a for-all type
*)
Ltac2 rec get_prod_binders (x : constr) : binder list :=
  match Constr.Unsafe.kind x with
  | Constr.Unsafe.Prod a y => a :: get_prod_binders y
  | _ => []
  end.

Local Ltac2 _binder_name_equal (name : ident) (b : binder) :=
  match Constr.Binder.name b with
  | None => false
  | Some binder_name => Ident.equal name binder_name
  end.

(**
  Exceptions for internal use, they should not be
  visible to the end user, and in principle shouldn't occur.
*)
Ltac2 Type exn ::= [ Binder_not_found (message) ].

(**
  Helper function to get the type of a binder with a given
  name from a list of binders.
*)
Local Ltac2 _get_binder_type_from_binder_list (name : ident) (b_list : binder list) : constr :=
  match List.find_opt (_binder_name_equal name) b_list with
  | None => Control.throw (Binder_not_found (concat_list [of_string "The variable "; of_ident name; of_string " was not found."]))
  | Some b => Constr.Binder.type b
  end.

Local Definition id {T : Type} (x : T) : T := x.

(**
  Find out which binders in the goal come with an
  immediate implication from a set i.e. which binders occur as in
  [forall b, b ∈ B -> ...]

  Returns:
    [((binder * constr * ident * int) list) * int] -
      the list contains all binders [b] for which the forall statement
      is immediately followed by a statement of the form [b ∈ B -> ...]
      the binder variable in the list is just [b], the constr corresponds
      to [B], the ident is the name that was assigned to the binder,
      this is useful because some sets [B] may depend on the names assigned
      to previous binders. The final int corresponds to how many anonymous hypotheses there are in the beginning part of the goal, consisting of only
      forall-statements and implications.

      The int [j] in the list corresponds to the nr of the anonymous hypothesis corresponding to the statement [b ∈ B], in the sense that [b ∈ B]
      is the (final int - j)th anonymous hyp. This counting is improved
      in the get_binders_from_implication_from_goal below.
*)
Ltac2 rec get_binders_with_implication_from_goal_aux () :
  ((binder * constr * ident * int) list) * int :=
  let add_binder_cond_and_name (b : binder) (cond : constr) (w : ident) :=
    (let wH := Fresh.fresh (Fresh.Free.of_goal ()) @___aux_H in
                  intro $wH;
                  let (b_list, ct) := get_binders_with_implication_from_goal_aux () in
                  ((b, cond, w, ct) :: b_list, Int.add ct 1) ) in
  lazy_match! goal with
  | [ |- _ -> ?_x] =>
    let w := Fresh.fresh (Fresh.Free.of_goal ()) @___aux in
    intro $w;
    let (b_list, ct) := get_binders_with_implication_from_goal_aux () in
    (b_list, Int.add ct 1)
  | [ |- forall _ : _, _ ] =>
    match Constr.Unsafe.kind (Control.goal ()) with
    | Constr.Unsafe.Prod b _ =>
      match Constr.Binder.name b with
      | None =>
        let w := Fresh.fresh (Fresh.Free.of_goal ()) @___aux in
        intro $w;
        let (b_list, ct) := get_binders_with_implication_from_goal_aux () in
        (b_list, Int.add ct 1)
      | Some b_name =>
          let w_opt := Ident.of_string (String.concat "" ["_temp_sp_"; Ident.to_string b_name]) in
          let w := match w_opt with
            | None => Fresh.fresh (Fresh.Free.of_goal ()) @_temp_
            | Some w_id => Fresh.fresh (Fresh.Free.of_goal ()) w_id
            end in
          intro $w;
          (* Now check whether the next term satisfies the conditions to be immediately added as a goal... *)
          lazy_match! (Control.goal ()) with
          | (?cond -> _) =>
            match! cond  with
            | ?predicate ?var =>
              (* Check variable *)
              if Bool.and (constr_is_ident var w) (constr_does_not_contain_ident predicate w) then
                add_binder_cond_and_name b cond w
              else
                match! cond with
                | ?other_pred ?var_1 ?other_arg =>
                    if Bool.and (constr_is_ident var_1 w)
                      (Bool.and (constr_does_not_contain_ident other_pred w)
                                (constr_does_not_contain_ident other_arg w)) then
                      add_binder_cond_and_name b cond w
                    else
                      get_binders_with_implication_from_goal_aux ()
                | _ => get_binders_with_implication_from_goal_aux ()
              end
            | _ =>
              (* case forall but not followed by implication
                 from a membership of a set*)
              get_binders_with_implication_from_goal_aux ()
            end
          | _ =>
            (* case forall but not followed by implication *)
            get_binders_with_implication_from_goal_aux ()
          end
      end
    | _ => throw (of_string "Expected a product type");
      get_binders_with_implication_from_goal_aux ()
    end
  | [ |- _] => ([], 0)
  end.

(**
  Find out which binders in the goal come with an
  immediate implication from a set, i.e. which binders occur as in
  [forall b, b ∈ B -> ...]

  Returns:
    [((binder * constr * ident * int) list)] -
      the list contains all binders [b] for which the forall statement
      is immediately followed by a statement of the form [b ∈ B -> ...]
      the binder variable in the list is just [b], the constr corresponds
      to [B], the ident is the name that was assigned to the binder,
      this is useful because some sets [B] may depend on the names assigned
      to previous binders. The int in the list is the nr of the anonymous hypothesis corresponding to the statement [b ∈ B].
*)
Ltac2 get_binders_with_implication_from_goal () :
    (binder * constr * ident * int) list :=
  let (b_list, total) := get_binders_with_implication_from_goal_aux () in
  List.map (fun (b, c, id, i) =>
    (b, c, id, Int.sub total i)) b_list.

(**
  Find out which binders in the provided hypothesis come with an
  immediate implication from a set, i.e. which binders occur as in
  [forall b, b ∈ B -> ...]

  Returns:
    [((binder * constr * ident * int) list)] -
      the list contains all binders [b] for which the forall statement
      is immediately followed by a statement of the form [b ∈ B -> ...]
      the binder variable in the list is just [b], the constr corresponds
      to [B], the ident is the name that was assigned to the binder,
      this is useful because some sets [B] may depend on the names assigned
      to previous binders. The int in the list is the nr of the anonymous hypothesis corresponding to the statement [b ∈ B].
*)
Ltac2 get_binders_with_implication_from_hyp (hyp : constr) : (binder * constr * ident * int) list :=
  let hyp_constr := hyp in
  let hyp_type := Constr.type hyp_constr in
  let w := Fresh.fresh (Fresh.Free.of_goal ()) @___aux in
  assert (False -> $hyp_type) as $w;
  let b_list := Control.focus 1 1 (fun () =>
    let false_key := Fresh.fresh (Fresh.Free.of_goal ()) @__false_key in
    Std.intro (Some false_key) None;
    let binder_list :=
      get_binders_with_implication_from_goal () in
    let key := Control.hyp false_key in
    destruct $key;
    binder_list) in
  clear $w;
  b_list.

Open Scope subset_scope.

Ltac2 mutable test_insertion := fun () => ().

(**
  Specializes a hypothesis that starts with a for-all statement.

  The user supplies names and choices for the bound variables in a given
  hypothesis. The tactic then specializes the hypothesis with the given choices. The
  choices are allowed to contain clanks. The unnamed holes will be filled in
  with named evars based on the names of the bound variables.

  Arguments:
    - [var_choice_list : (ident * constr) list], list of names for variables together with choices for those variables
    - [in_hyp : ident], name of the hypothesis to specialize.

  Raises fatal exceptions:
    - If the hypothesis [in_hyp] does not start with a for-all statement.
*)
Local Ltac2 wp_specialize (var_choice_list : (ident * constr) list) (h:constr) :=
  let statement := eval unfold type_of in (type_of $h) in
  lazy_match! statement with
    | (* TODO: this can be relaxed, the code presumably also
         works with an implication *)
      _ -> ?_x => (* Exclude matching on functions (naming codomain necessary) *)
      throw (of_string "`Use ... in (*)` only works if (*) starts with a for-all quantifier.")
    | forall _ : _, _ =>
      (* Create new hypotheses *)
      let binder_types :=
        match Control.case (fun () => get_binders_with_implication_from_hyp h) with
        | Val (x, _) => x
        | Err exn => warn (concat_list [of_string "Could not understand the structure with the involved sets. A simplified version of 'Use' is used.";
      fnl () ; of_string "This is a not a problem, but you may report this example, mentioning the exception:"; fnl (); of_exn exn]); []
        end in
      let w := Fresh.fresh (Fresh.Free.of_goal ()) @_H in
      (* The introduction of helper definition was added for Coq v8.18 since otherwise
         one would get an error saying that one cannot instantiate the evar.
         We build variable names for the helper variables from the
         binder name, in the hope to avoid naming conflicts. *)
      let def_list :=
        List.map (fun (i, c) =>
          (* this is our guess for what binders get renamed to *)
          let id_opt :=
              Ident.of_string (String.concat "" ["_temp_sp_"; Ident.to_string i]) in
          let aux_x := match id_opt with
          | None => Fresh.fresh (Fresh.Free.of_goal ()) @_aux_sp_
          | Some temp_id => Fresh.fresh (Fresh.Free.of_goal ()) temp_id
          end in
          pose ($aux_x := $c);
          (i, aux_x)) var_choice_list in
      let wrapped_var_choice_list :=
        List.map (fun (i, aux_x) => (i, Control.hyp aux_x)) def_list in
      (* specialize *)
      Std.specialize (h, Std.ExplicitBindings
        (_ident_to_hyp_list wrapped_var_choice_list))
        (Some (Std.IntroNaming (Std.IntroIdentifier w)));
      (* warn user that gaps need to be filled in *)
      let evars := _names_evars var_choice_list in
      match is_empty evars with
      | true => ()
      | false => warn (concat_list (
          [of_string "Please come back to this line later to make a definite choice for ";
            _of_idents evars; of_string "."]));
          assert_fix_earlier_warning ()
      end;
      (* Rename the blank evars in the terms supplied by the user,
        in such a way that the base name is derived from the binder name. *)
      List.fold_right (fun (i, c) () =>
        rename_blank_evars_in_term (Ident.to_string i) c) var_choice_list ();
      (* Since the code is rather hacky, we're gonna wrap the part that
         tries to address the set memberships in a try-catch block. *)
      match Control.case ( fun () =>
        (* For testing purposes, can force this to throw an error *)
        test_insertion ();
        (* Add the statments that variables are in sets as new subgoals *)
        let new_hyp_list :=
          List.fold_left (fun prev_id_list (_, con, id, nr)  =>
          (* Only do something for the binders that the caller provided *)
          match List.find_opt (fun (_, aux_x) =>
            Ident.equal id aux_x) def_list with
          | None => prev_id_list
          | Some (_, _) =>
            Control.focus 1 1 (fun () =>
              let aux_id := Fresh.fresh (Fresh.Free.of_goal ()) @_H in
              (* add the subgoal *)
              enough ($con) as $aux_id;
              (nr, aux_id) :: prev_id_list)
          end) [] binder_types in
        Control.focus 1 1 (fun () =>
        let constr_w := Control.hyp w in
        (* In the specialized statement, now also use the proved
           set memberships *)
        Std.specialize (constr_w, Std.ExplicitBindings
        (List.map (fun (nr, aux_id) =>
          let aux_id_c := Control.hyp aux_id in
          (Std.AnonHyp nr, aux_id_c)) new_hyp_list))
        None);
        (* Wrap all set-membership goals *)
        Control.focus 2 (Int.add (List.length new_hyp_list) 1) (fun () =>
          apply StateGoal.unwrap)) with
      | Val _ => ()
      | Err exn => warn (concat_list [of_string "Could not understand the structure with the involved sets. A simplified version of 'Use' is used.";
      fnl () ; of_string "This is a not a problem, but you may report this example, mentioning the exception:"; fnl (); of_exn exn])
      end;
      (* Wrap the goal *)
      Control.focus 1 1 (fun () =>
        let new_w_c := Control.hyp w in
        let new_w_t := Constr.type new_w_c in
        apply (StateHyp.unwrap $new_w_t $new_w_c));
      (* revert the order of the goals, so the order is natural *)
      ltac1:(revgoals);
      (* substitute the temporary definitions *)
      List.iter (fun (_, c) => subst $c) def_list
    | _ => throw (of_string "`Use ... in (*)` only works if (*) starts with a for-all quantifier.")
  end.

Ltac2 wp_specialize_one (var_choice : ident * ident) (id : ident) :=
  let h := Control.hyp id in
  let type_of_h := Constr.type h in
  let (var, choice) := var_choice in
  let is_sealed :=
    lazy_match! (Constr.type h) with
    | seal _ _ => true
    | _ => false
    end in
  let statement :=
    if is_sealed then
      (eval unfold seal at 1 in $type_of_h)
    else type_of_h in
  match check_binder_name statement var false with
  | None => ()
  | Some first_guessed_name =>
    match check_binder_name statement var true with
    | None => ()
    | Some second_guessed_name =>
      if Ident.equal first_guessed_name second_guessed_name then
        warn (concat_list [of_string "Expected variable name ";  of_ident first_guessed_name;
          of_string " instead of "; of_ident var; of_string "."])
      else
        warn (concat_list [of_string "Expected variable name "; of_ident first_guessed_name;
          of_string " or " ;
          of_ident second_guessed_name; of_string " instead of " ; of_ident var;
          of_string "."])
    end
  end;
  let aux_id := Fresh.fresh (Fresh.Free.of_goal ()) @_aux in
  assert $statement as $aux_id;
  Control.focus 1 1 (fun () => exact $h);
  let aux_c := Control.hyp aux_id in
  let choice_c := Control.hyp choice in
  specialize ($aux_c $choice_c);
  if is_sealed then
    let aux_c := Control.hyp aux_id in
    lazy_match! (Constr.type aux_c) with
    | ?con -> _ =>
        let w := Fresh.fresh (Fresh.Free.of_goal ()) @_H in
        enough ($con) as $w;
        Control.focus 2 2 (fun () =>
          unfold ge_op, R_ge_type, nat_ge_type, gt_op, R_gt_type, nat_gt_type,
          lt_op, R_lt_type, nat_lt_type, le_op, R_le_type, nat_le_type;
          apply VerifyGoal.unwrap);
        Control.focus 1 1 (fun () =>
          let w_c := Control.hyp w in
          specialize ($aux_c $w_c))
    | _ => () (* TODO: should we throw an error here? one should never arrive in this case ... *)
    end
  else ();
  Std.rename [(id, aux_id); (aux_id, id)];
  Std.clear [aux_id].

(**
  Specializes a hypothesis that starts with a for-all statement.

  The user supplies names and choices for the bound variables in a given
  hypothesis. The tactic then specializes the hypothesis with the given choices. The
  choices are allowed to contain clanks. The unnamed holes will be filled in
  with named evars based on the names of the bound variables.

  Arguments:
    - [var_choice_list : (ident * constr) list], list of names for variables together with choices for those variables
    - [in_hyp : ident], name of the hypothesis to specialize.

  Raises fatal exceptions:
    - If the hypothesis [in_hyp] does not start with a for-all statement.
*)
Local Ltac2 wp_specialize' (var_choice_list : (ident * constr) list) (h:constr) :=
  let possibly_sealed_statement :=
     eval unfold type_of in (type_of $h) in
  let statement :=
    match! possibly_sealed_statement with
    | seal _ _ => eval unfold seal at 1 in $possibly_sealed_statement
    | _ => possibly_sealed_statement
    end in
  let aux_id := Fresh.fresh (Fresh.Free.of_goal ()) @_H in
  assert $possibly_sealed_statement as $aux_id;
  Control.focus 1 1 (fun () => exact $h);
  (* The introduction of helper definitions was added for Coq v8.18 since otherwise
    one would get an error saying that one cannot instantiate the evar.
    We build variable names for the helper variables from the
    binder name, in the hope to avoid naming conflicts. *)
  let def_list :=
    List.map (fun (i, c) =>
      (* this is our guess for what binders get renamed to *)
      let id_opt :=
          Ident.of_string (String.concat "" ["_temp_sp_"; Ident.to_string i]) in
      let aux_x := match id_opt with
      | None => Fresh.fresh (Fresh.Free.of_goal ()) @_aux_sp_
      | Some temp_id => Fresh.fresh (Fresh.Free.of_goal ()) temp_id
      end in
      set ($aux_x := $c);
      (i, aux_x)) var_choice_list in
  let evars := _names_evars var_choice_list in
  match is_empty evars with
  | true => ()
  | false => warn (concat_list (
      [of_string "Please come back to this line later to make a definite choice for ";
        _of_idents evars; of_string "."]));
      assert_fix_earlier_warning ()
  end;
  lazy_match! statement with
    | _ -> ?_x => (* Exclude matching on functions (naming codomain necessary) *)
      throw (of_string "`Use ... in (*)` only works if (*) starts with a for-all quantifier.")
    | forall _ : _, _ =>
      (* Create new hypotheses *)
      List.iter (fun x => Control.focus 1 1 (fun () => wp_specialize_one x aux_id)) def_list;
      Control.focus 1 1 (fun () =>
        let new_w_c := Control.hyp aux_id in
        let new_w_t := Constr.type new_w_c in
      List.iter (fun (i, c) =>
        rename_blank_evars_in_term (Ident.to_string i) c) var_choice_list;
      apply (StateHyp.unwrap $new_w_t $new_w_c));
      List.iter (fun (_, c) => subst $c) def_list;
      ltac1:(revgoals)
      (* still need to restate the goal *)
    | _ => throw (of_string "`Use ... in (*)` only works if (*) starts with a for-all quantifier.")
  end.


(**
  Specializes a hypothesis that starts with a for-all statement.

  Arguments:
    - [var_choice_list : (ident * constr) list], list of names for variables
        together with choices for those variables
    - [in_hyp : ident], name of the hypothesis to specialize.

  Raises fatal exceptions:
    - If the hypothesis [in_hyp] does not start with a for-all statement.
*)
Ltac2 Notation "Use" var_choice_list(list1(seq(ident, ":=", open_constr), ","))
    "in" "(" in_hyp(constr) ")" :=
  panic_if_goal_wrapped ();
  wp_specialize' var_choice_list in_hyp.
