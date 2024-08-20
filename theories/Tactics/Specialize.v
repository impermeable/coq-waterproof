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


(**
  Specializes a hypothesis that starts with a for-all statement.
    
  Arguments:
    - [var_choice_list : (ident * constr) list], list of names for variables together with choices for those variables 
    - [in_hyp : ident], name of the hypothesis to specialize.

  Raises fatal exceptions:
    - If the hypothesis [in_hyp] does not start with a for-all statement.
*)

Local Ltac2 _ident_to_hyp_list (ls : (ident * constr) list) : (Std.hypothesis * constr) list 
 := List.map (fun (i, x) => (Std.NamedHyp i, x)) ls.

Local Ltac2 _names_evars (ls : (ident * constr) list) : ident list
 := List.map (fun (i, x) => i) (List.filter (fun (i, x) => Constr.has_evar x) ls).

Local Ltac2 rec _of_idents (xs : ident list) : message
 := match List.rev(xs) with
    | t::[] => of_ident t
    | t::ls => concat_list [_of_idents (List.rev(ls)); of_string ", "; of_ident t]
    | [] => of_string ""  (* not used *)
    end.

Local Ltac2 is_empty (ls : 'a list) : bool
 := match ls with
    | _::_ => false
    | [] => true
    end.

Local Ltac2 wp_specialize (var_choice_list : (ident * constr) list) (h:constr) :=
  let statement := eval unfold type_of in (type_of $h) in
  lazy_match! statement with
    | _ -> ?x => (* Exclude matching on functions (naming codomain necessary) *)
      throw (of_string "`Pick ... in (*)` only works if (*) starts with a for-all quantifier.")
    | forall _ : _, _ =>
      let w := Fresh.fresh (Fresh.Free.of_goal ()) @_H in
      (* specialize *)
      Std.specialize (h, Std.ExplicitBindings (_ident_to_hyp_list var_choice_list)) 
        (Some (Std.IntroNaming (Std.IntroIdentifier w))) ;
      (* get output *)
      let constr_w := Control.hyp w in
      let type_w := Constr.type constr_w in
      (* warn user that gap needs to be filled in *)
      let evars := _names_evars var_choice_list in
      match is_empty evars with
      | true => ()
      | false => warn (concat_list (
          [of_string "Please come back to this line later to make a definite choice for ";
            _of_idents evars; of_string "."]))
      end;
      (* Wrap the goal *)
      apply (StateHyp.unwrap $type_w $constr_w)
    | _ => throw (of_string "`Pick ... in (*)` only works if (*) starts with a for-all quantifier.")
  end.

(**
  Specializes a hypothesis that starts with a for-all statement.
    
  Arguments:
    - [var_choice_list : (ident * constr) list], list of names for variables together with choices for those variables 
    - [in_hyp : ident], name of the hypothesis to specialize.

  Raises fatal exceptions:
    - If the hypothesis [in_hyp] does not start with a for-all statement.
*)
Ltac2 Notation "Use" s(list1(seq(ident, ":=", open_constr), ",")) "in" "(" in_hyp(constr) ")" :=
  wp_specialize s in_hyp.



