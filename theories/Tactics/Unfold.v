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

(** * Tactics that wrap the goal such that the user needs to specify the effect of unfolding in the proof script. *)


Ltac2 ap_goal_unwrap () := apply ExpandDef.Goal.unwrap.

Ltac2 ident_to_clause (h : ident) :=
  {Std.on_hyps := Some [(h, Std.AllOccurrences, Std.InHyp)]; 
  Std.on_concl := Std.NoOccurrences}.

Ltac2 ap_hyp_unwrap (h : constr) := apply (fun G => ExpandDef.Hyp.unwrap G _ $h).


(**
  Rewrite a function by its definition, in the goal or in a *single* hypothesis.

  Arguments:
    - [targets: constr] or [targets: constr list], the target function to unfold, or the target functions (separated by [,]) to unfold.
    - [cl: constr], optional suffix with syntax [... in h] for some [h], where [h] is the hypothesis to rewrite the function [f] in.
      If omitted, [f] is rewritten in the goal.

  Raises fatal exceptions:
    - If the identifier [h] in the suffix [... in h] is not an hypothesis.
 
*)
Ltac2 Notation "Expand" "the" "definition" "of" targets(list1(seq(reference, occurrences), ",")) cl(opt(seq("in", "(", ident, ")"))) :=
  panic_if_goal_wrapped ();
  match cl with
    | None => 
      Std.unfold targets (Notations.default_on_concl None);
      ap_goal_unwrap ()
    | Some cl => 
      let h_constr := Control.hyp cl in
      Std.unfold targets (ident_to_clause cl);
      ap_hyp_unwrap h_constr
  end.


Ltac2 expand_def_framework (unfold_goal : unit -> unit) (unfold_hyp : ident -> unit) (cl : ident option):=
  panic_if_goal_wrapped ();
  match cl with
    | None =>
      unfold_goal ();
      ap_goal_unwrap ()
    | Some cl =>
      let h_constr := Control.hyp cl in (* throws error if ident not found in hypotheses *)
      unfold_hyp cl;
      ap_hyp_unwrap h_constr
  end.


(**
  Removes the [ExpandDef.Goal.Wrapper] from the goal.

  Arguments:
    - [t: constr], the rewritten goal.
  
  Raises fatal exceptions:
    - If [t] is not syntactically the same as the goal [G] in the wrapper [ExpandDef.Goal.Wrapper G].
    - If the current goal is not wrapped in the [ExpandDef.Goal.Wrapper].
*)
Ltac2 goal_as (t:constr) := 
  lazy_match! goal with
    | [|- ExpandDef.Goal.Wrapper ?v] =>
      match Constr.equal v t with
        | true => apply (ExpandDef.Goal.wrap); change $t
        | false => throw (of_string "Wrong goal specified.")
      end
    | [|- ExpandDef.Hyp.Wrapper _ _ _] => throw (of_string "Specify the effect of expanding definition in *hypothesis*.")
    | [|- _] => throw (of_string "No need to specify the effect of expanding definition.")
  end.

Ltac2 Notation "That" "is," "write" "the" "goal" "as" t(constr) := goal_as t.


(**
  Removes the [ExpandDef.Hyp.Wrapper] from the goal.

  Arguments:
    - [h : ident], the hypothesis that has been rewritten.
    - [t: constr], the type the hypotheis has been rewritten as.

  Raises fatal exceptions:
    - If the wrapped goal is not of the form [ExpandDef.Hyp.Wrapper _ t h], that is, h or t has been specified incorrectly.
    - If the current goal is not wrapped in the [ExpandDef.Hyp.Wrapper]. 
*)
Ltac2 hyp_as (h : ident) (t:constr) :=
  let h_hyp := Control.hyp h in
  lazy_match! goal with
    | [|- ExpandDef.Hyp.Wrapper _ ?s ?g] =>
      match Constr.equal s t with
        | true => 
          match Constr.equal g h_hyp with
            | true => apply (fun G => ExpandDef.Hyp.wrap G $s $g); change $t in $h
            | false => throw (of_string "Wrong statement specified.")
          end
        | false => throw (of_string "Wrong statement specified.")
      end
    | [|- ExpandDef.Goal.Wrapper _] => throw (of_string "Specify the effect of expanding definition in *goal*.")
    | [|- _] => throw (of_string "No need to specify the effect of expanding definition.")
  end.

Ltac2 Notation "That" "is," "write" "(" h(ident) ")" "as" t(constr) := hyp_as h t.
