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

Require Import Util.Constr.
Require Import Util.Goals.
Require Import Util.Hypothesis.
Require Import Util.MessagesToUser.
Require Import Waterprove.

(* Switch order of decidable goal. *)
Local Lemma sumbool_comm (A B : Prop) : {A} + {B} -> {B} + {A}.
Proof.
  intro H.
  induction H.
  right; exact a.
  left; exact b.
Qed.

(**
  Split the proof by case distinction when the goal is a prop

  Arguments:
    - [t1 : constr], the first case.
    - [t2 : constr], the second case.

  Does:
    - splits the proof by case distinction; wraps the resulting goals in the Case.Wrapper
*)
Ltac2 either_or_prop (t1:constr) (t2:constr) :=
  let h_id := Fresh.in_goal @_temp in
  let attempt () :=
    assert ($t1 \/ $t2) as $h_id;
    Control.focus 1 1 (fun () => 
      let automation () := waterprove 4 false Decidability in
      first 
        [ 
          automation ()
          | apply or_comm; automation ()
        ]
    ) in
    match Control.case attempt with
      | Val _ =>
        let h_val := Control.hyp h_id in
        destruct $h_val;
        Control.focus 1 1 (fun () => apply (Case.unwrap $t1));
        Control.focus 2 2 (fun () => apply (Case.unwrap $t2))
      | Err exn => throw (Message.of_string "Could not find a proof that the first or the second statement holds.")
    end.

(**
  Split the proof by case distinction when the goal is not a prop

  Arguments:
    - [t1 : constr], the first case.
    - [t2 : constr], the second case.

  Does:
    - splits the proof by case distinction; wraps the resulting goals in the Case.Wrapper
*)
Ltac2 either_or_type (t1:constr) (t2:constr) :=
  let h_id := Fresh.in_goal @_temp in
  let attempt () :=
    assert ({$t1} + {$t2}) as $h_id;
    Control.focus 1 1 (fun () => 
      let automation () := waterprove 3 false Decidability in
      first 
        [ 
          automation ()
          | apply sumbool_comm; automation ()
        ]
    ) in
    match Control.case attempt with
      | Val _ =>
        let h_val := Control.hyp h_id in
        destruct $h_val;
        Control.focus 1 1 (fun () => apply (Case.unwrap $t1));
        Control.focus 2 2 (fun () => apply (Case.unwrap $t2))
      | Err exn => throw (Message.of_string "Could not find a proof that the first or the second statement holds.")
    end.

(**
  Split the proof by case distinction.

  Arguments:
    - [t1 : constr], the first case.
    - [t2 : constr], the second case.

  Does:
    - splits the proof by case distinction; wraps the resulting goals in the Case.Wrapper
*)
Ltac2 either_or (t1:constr) (t2:constr) :=
  let goal_is_prop := 
    lazy_match! goal with
      | [ |- ?u] => 
        (* Check whether [u] is not a proposition. *)
        let sort_u := get_value_of_hyp(u) in
        check_constr_equal sort_u constr:(Prop)
    end
  in
  if goal_is_prop 
    then either_or_prop t1 t2
    else either_or_type t1 t2. 

Ltac2 Notation "Either" t1(constr) "or" t2(constr) := 
  panic_if_goal_wrapped ();
  either_or t1 t2.

(* Type that enables a three-case distiction to be solved with three bullets that are of the same level. *)
Inductive sumtriad (A B C : Prop): Set :=
  | left   : A -> sumtriad A B C
  | middle : B -> sumtriad A B C
  | right  : C -> sumtriad A B C.

Arguments left   {A B C} _.
Arguments middle {A B C} _.
Arguments right  {A B C} _.

(* Lemmas that enable the searching of hints whose cases are ordered differently than the user's input. *)
Local Lemma double_sumbool_sumtriad_abc (A B C : Prop) : {A} + {B} + {C} -> sumtriad A B C.
Proof.
  intro H.
  induction H as [[a | b] | c].
  exact (left a).
  exact (middle b).
  exact (right c).
Qed.

Local Lemma double_sumbool_sumtriad_acb (A B C : Prop) : {A} + {C} + {B} -> sumtriad A B C.
Proof.
  intro H.
  induction H as [[a | c] | b].
  exact (left a). exact (right c).
  exact (middle b).
Qed.

Local Lemma double_sumbool_sumtriad_bac (A B C : Prop) : {B} + {A} + {C} -> sumtriad A B C.
Proof.
  intro H.
  induction H as [[b | a] | c].
  exact (middle b).
  exact (left a).
  exact (right c).
Qed.

Local Lemma double_sumbool_sumtriad_bca (A B C : Prop) : {B} + {C} + {A} -> sumtriad A B C.
Proof.
  intro H.
  induction H as [[b | c] | a].
  exact (middle b).
  exact (right c).
  exact (left a).
Qed.

Local Lemma double_sumbool_sumtriad_cab (A B C : Prop) : {C} + {A} + {B} -> sumtriad A B C.
Proof.
  intro H.
  induction H as [[c | a] | b].
  exact (right c).
  exact (left a).
  exact (middle b).
Qed.

Local Lemma double_sumbool_sumtriad_cba (A B C : Prop) : {C} + {B} + {A} -> sumtriad A B C.
Proof.
  intro H.
  induction H as [[c | b] | a].
  exact (right c).
  exact (middle b).
  exact (left a).
Qed.

(**
  Split the proof by case distinction if the goal is a prop.

  Arguments:
    - [t1 : constr], the first case.
    - [t2 : constr], the second case.
    - [t3 : constr], the third case.

  Does:
    - splits the proof by case distinction; wraps the resulting goals in the Case.Wrapper
*)
Ltac2 either_or_or_prop (t1:constr) (t2:constr) (t3:constr) :=
  let h1_id := Fresh.in_goal @_temp in
  let attempt () :=
    assert ($t1 \/ $t2 \/ $t3) as $h1_id;
    Control.focus 1 1 (fun () => 
      let automation () := waterprove 4 false Decidability in
      let g := Control.goal () in first 
      [ 
        automation ()
      ]
    )
  in
  match Control.case attempt with
    | Val _ =>
      let h2_id := Fresh.in_goal @_temp in
      let h_val := Control.hyp h1_id in
      destruct $h_val as [_ | $h2_id];
      Control.focus 1 1 (fun () => apply (Case.unwrap $t1));
      Control.focus 2 2 (fun () => 
        let h2_val := Control.hyp h2_id in
        destruct $h2_val;
        Control.focus 1 1 (fun () => apply (Case.unwrap $t2));
        Control.focus 2 2 (fun () => apply (Case.unwrap $t3)))
    | Err exn => throw (Message.of_string "Could not find a proof that the first, the second or the third statement holds.")
  end.

(**
  Split the proof by case distinction if the goal is not a prop.

  Arguments:
    - [t1 : constr], the first case.
    - [t2 : constr], the second case.
    - [t3 : constr], the third case.

  Does:
    - splits the proof by case distinction; wraps the resulting goals in the Case.Wrapper
*)
Ltac2 either_or_or_type (t1:constr) (t2:constr) (t3:constr) :=
  let h_id := Fresh.in_goal @_temp in
  let attempt () :=
    assert (sumtriad $t1 $t2 $t3) as $h_id;
    Control.focus 1 1 (fun () => 
      let automation () := waterprove 3 false Decidability in
      let g := Control.goal () in first 
      [ 
        apply double_sumbool_sumtriad_abc; automation ()
      | apply double_sumbool_sumtriad_acb; automation ()
      | apply double_sumbool_sumtriad_bac; automation ()
      | apply double_sumbool_sumtriad_bca; automation ()
      | apply double_sumbool_sumtriad_cab; automation ()
      | apply double_sumbool_sumtriad_cba; automation ()
      ]
    )
  in
  match Control.case attempt with
    | Val _ =>
      let h_val := Control.hyp h_id in
      destruct $h_val;
      Control.focus 1 1 (fun () => apply (Case.unwrap $t1));
      Control.focus 2 2 (fun () => apply (Case.unwrap $t2));
      Control.focus 3 3 (fun () => apply (Case.unwrap $t3))
    | Err exn => throw (Message.of_string "Could not find a proof that the first, the second or the third statement holds.")
  end.

(**
  Split the proof by case distinction.

  Arguments:
    - [t1 : constr], the first case.
    - [t2 : constr], the second case.
    - [t3 : constr], the third case.

  Does:
    - splits the proof by case distinction; wraps the resulting goals in the Case.Wrapper
*)
Ltac2 either_or_or (t1:constr) (t2:constr) (t3:constr) :=
  lazy_match! goal with
    | [ |- ?u] => 
      (* Check whether [u] is not a proposition. *)
      let sort_u := get_value_of_hyp(u) in
      if (check_constr_equal sort_u constr:(Prop))
      then either_or_or_prop t1 t2 t3
      else either_or_or_type t1 t2 t3
  end.

Ltac2 Notation "Either" t1(constr) "," t2(constr) "or" t3(constr) := 
  panic_if_goal_wrapped ();
  either_or_or t1 t2 t3.
