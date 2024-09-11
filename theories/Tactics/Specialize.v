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
Require Import Util.Goals.
Require Import Util.MessagesToUser.
Require Import Util.Evars.

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
 := List.map (fun (i, x) => i) (List.filter (fun (i, x) => Constr.has_evar x) ls).

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
    | _ -> ?x => (* Exclude matching on functions (naming codomain necessary) *)
      throw (of_string "`Use ... in (*)` only works if (*) starts with a for-all quantifier.")
    | forall _ : _, _ =>
      let w := Fresh.fresh (Fresh.Free.of_goal ()) @_H in
      (* specialize *)
      Std.specialize (h, Std.ExplicitBindings (_ident_to_hyp_list var_choice_list))
        (Some (Std.IntroNaming (Std.IntroIdentifier w))) ;
      (* get output *)
      let constr_w := Control.hyp w in
      let type_w := Constr.type constr_w in      
      (* warn user that gaps need to be filled in *)
      let evars := _names_evars var_choice_list in
      match is_empty evars with
      | true => ()
      | false => warn (concat_list (
          [of_string "Please come back to this line later to make a definite choice for ";
            _of_idents evars; of_string "."]))
      end;
      (* Rename the blank evars in the terms supplied by the user,
         in such a way that the base name is derived from the binder name. *)
      List.fold_right (fun (i, c) () =>
        rename_blank_evars_in_term (Ident.to_string i) c) () var_choice_list;
      (* Wrap the goal *)
      apply (StateHyp.unwrap $type_w $constr_w)
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
  wp_specialize var_choice_list in_hyp.
