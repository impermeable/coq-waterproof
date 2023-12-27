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

Require Import Classical.
Require Import Ltac2.Ltac2.
Require Import Ltac2.Message.
Local Ltac2 concat_list (ls : message list) : message :=
  List.fold_right concat (of_string "") ls.

Require Import Util.Init.
Local Ltac2 get_type (x: constr) : constr := eval unfold type_of in (type_of $x).

Require Import Util.Goals.
Require Import Util.MessagesToUser.
Require Import Waterprove.


(**
  Starts a proof by contradiction.

  Arguments:
    - no arguments.

  Does:
    - Replaces the goal [G] by its double negation [¬ ¬ G].
*)
Ltac2 contra () :=
  lazy_match! goal with
    | [ |- ?x] =>
      apply (NNPP $x);
      apply (ByContradiction.unwrap (not $x))
  end.


(**
  Attempts to solve the goal by finding a contradiction to the previous statement.

  Arguments:
    - no arguments.

  Does:
    - If last hypothesis is of the form ~P, tries to find a proof of P and finish the
      proof with the resulting contradiction.
    - If last hypothesis is of the form P, tries to find a proof of ~P and finish the
      proof with the resulting contradiction.
    - Throws an error if no hypohteses, or if last hypothesis cannot be negated.
*)

Ltac2 contradiction () := 
  lazy_match! goal with
  | [ id_h : _ |- _ ] =>
    let h := Control.hyp id_h in
    let prop_h := get_type h in
    let id_contra := Fresh.in_goal @_Hcontra in
    lazy_match! prop_h with
    | ~ ?p => 
      (* Try to find a proof of p *)
      match Control.case (fun () =>
        assert $p as $id_contra by
          (waterprove 5 true Main))
      with
      | Err (FailedToProve g) => throw (concat_list
        [of_string "Could not verify that "; of_constr g; of_string "."])
      | Err exn => Control.zero exn
      | Val _ =>
        let p := Control.hyp id_contra in
        apply False_rect;
        exact ($h $p)
      end
    | ?p =>
      (* Try to find a proof of ~p *)
      match Control.case (fun () =>
        assert (~ $p) as $id_contra)
      with
      | Err exn => throw (concat_list
        [of_string "Previous statement cannot be negated."])
      | Val _ =>
        match Control.case (fun () => Control.focus 1 1 (fun () =>
          (waterprove 5 true Main)))
        with
        | Err (FailedToProve g) => throw (concat_list
          [of_string "Could not verify that "; of_constr g; of_string "."])
        | Err exn => Control.zero exn
        | Val _ =>
          let not_p := Control.hyp id_contra in
          apply False_rect;
          exact ($not_p $h)
        end
      end
    end
  | [ |- _ ] => throw (of_string "No statement to contradict.")
  end.

Ltac2 Notation "We" "argue" "by" "contradiction" := contra ().

Ltac2 Notation "Contradiction" := 
  panic_if_goal_wrapped ();
  contradiction ().

Ltac2 Notation "↯" := 
  panic_if_goal_wrapped ();
  contradiction ().