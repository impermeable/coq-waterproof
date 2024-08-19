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

Local Ltac2 _ident_to_hyp_list (ls : (ident * constr) list) : (Std.hypothesis * constr) list 
:= List.map (fun (i, x) => (Std.NamedHyp i, x)) ls.

Local Ltac2 wp_specialize (var_choice_list : (ident * constr) list) (h:constr) :=
  (* let h := Control.hyp in_hyp in *)
  (* let named_hyp := Std.NamedHyp s in *)
  let statement := eval unfold type_of in (type_of $h) in
  (* let specialized_statement := eval unfold type_of in (type_of ($h $choice)) in *)
  lazy_match! statement with
    | _ -> ?x => (* Exclude matching on functions (naming codomain necessary) *)
      throw (of_string "`Pick ... in (*)` only works if (*) starts with a for-all quantifier.")
    | forall _ : _, _ =>
      let w := Fresh.fresh (Fresh.Free.of_goal ()) @_H in
      Std.specialize (h, Std.ExplicitBindings (_ident_to_hyp_list var_choice_list)) 
        (Some (Std.IntroNaming (Std.IntroIdentifier w))) ;
      (* specialize $h with ($named_hyp := $choice) as $w; *)
      (* Wrap the goal *)
      let constr_w := Control.hyp w in
      let type_w := Constr.type constr_w in
      apply (StateHyp.unwrap $type_w $constr_w)
    | _ => throw (of_string "`Pick ... in (*)` only works if (*) starts with a for-all quantifier.")
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
Ltac2 Notation "Use" s(list1(seq(ident, ":=", constr), ",")) "in" "(" in_hyp(constr) ")" :=
  wp_specialize s in_hyp.
