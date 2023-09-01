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

Require Import Coq.Reals.Reals.

Require Import Logic.ClassicalEpsilon.

Require Import Automation.
Require Import Notations.
Require Import Tactics.
Require Import Util.Lock.

Open Scope R_scope.

Waterproof Enable Automation RealsAndIntegers.
Waterproof Enable Automation Intuition.


(** Functions used for using and expanding definitions *)

Require Import Logic.FunctionalExtensionality.
Require Import Logic.PropExtensionality.

Require Import Util.Init.
Require Import Ltac2.Message.
Local Ltac2 get_type (x: constr) : constr := eval unfold type_of in (type_of $x).
Local Ltac2 concat_list (ls : message list) : message :=
  List.fold_right concat (of_string "") ls.

(* Set Default Timeout 3. *)


(** Definitions and notation for non-emptyness and boundedness. *)

(** Non-empty *)
(* Definition *)
Definition is_non_empty (A : R -> Prop) := 
  locked (there exists x : R, A x).
Notation "'_non_empty_def_type'" := 
  (fun (A : R -> Prop) => there exists x : R, A x) (at level 69, only parsing).
Lemma definition_non_empty (A : R -> Prop) :
  is_non_empty A   <->  _non_empty_def_type A.
Proof. unfold is_non_empty; rewrite <- lock; reflexivity. Qed.
(* Hint for using definition *)
Lemma _rule_def_non_empty 
  (def : forall A : R -> Prop, is_non_empty A <-> _non_empty_def_type A) :
  is_non_empty   =   _non_empty_def_type.
Proof.
  apply functional_extensionality; intro A.
  apply propositional_extensionality. apply def.
Qed.
Local Ltac2 use_def_non_empty_in_goal () :=
  let def_id := Fresh.in_goal @_temp in
  enough (forall A : R -> Prop, is_non_empty A <-> _non_empty_def_type A) as $def_id;
  Control.focus 1 1 (fun () => 
    let def := Control.hyp def_id in
    rewrite (_rule_def_non_empty $def); assumption
  ).
Local Ltac2 use_def_non_empty_in_hyp () :=
  match! goal with
  | [ h : _ |- _ ] =>
    let def_id := Fresh.in_goal @_temp in
    enough (forall A : R -> Prop, is_non_empty A <-> _non_empty_def_type A) as $def_id;
    Control.focus 1 1 (fun () => 
      let def := Control.hyp def_id in
      rewrite (_rule_def_non_empty $def) in $h;
      let h_constr := Control.hyp h in apply $h_constr
    )
  end.
#[export] Hint Extern 1 => ltac2:(use_def_non_empty_in_goal ()) : wp_definitions.
#[export] Hint Extern 1 => ltac2:(use_def_non_empty_in_hyp ()) : wp_definitions.
  Notation "A 'is' '_non-empty_'" := (is_non_empty A) (at level 69).
  Notation "A 'is' 'non-empty'" := (is_non_empty A) (at level 69, only parsing).

(* Tactic for expanding definition *)
Local Ltac2 exp_def_non_empty (t : constr) :=
  lazy_match! t with
  | context [ is_non_empty ?a ] => 
    let def := get_type constr:(definition_non_empty $a) in
    print (of_string "");
    print (concat (of_constr constr:(definition_non_empty)) (of_string ":"));
    print (concat (of_string "    ") (of_constr def))
  | _ => 
    print (of_string ""); 
    print (concat (of_string "'non-empty' does not occur in ") (of_constr t))
  end.
Ltac2 Notation "Expand" "the" "definition" "of" "non-empty" "in" t(constr) := 
  exp_def_non_empty t.
(* Notation *)



(** is an upper bound *)
(* Definition *)
Definition is_upper_bound (A : R -> Prop) (M : R) :=
  locked (for all a : R, A a -> a <= M).
Notation "'_upper_bound_def_type'" := 
  (fun (A : R -> Prop) (M : R) => for all a : R, A a -> a <= M) (at level 69, only parsing).
Lemma definition_upper_bound (A : R -> Prop) (M : R) : 
  is_upper_bound A M   <->   _upper_bound_def_type A M.
Proof. unfold is_upper_bound; rewrite <- lock; reflexivity. Qed.
(* Hint for using definition *)
Lemma _rule_def_upper_bound 
  (def : forall (A : R -> Prop) (M : R), 
    is_upper_bound A M <-> _upper_bound_def_type A M) :
  is_upper_bound   =   _upper_bound_def_type.
Proof.
  apply functional_extensionality; intro A.
  apply functional_extensionality; intro M.
  apply propositional_extensionality; apply def.
Qed.
Local Ltac2 use_def_upper_bound_in_goal () :=
  let def_id := Fresh.in_goal @_temp in
  enough (forall (A : R -> Prop) (M : R), is_upper_bound A M <-> _upper_bound_def_type A M) as $def_id;
  Control.focus 1 1 (fun () => 
    let def := Control.hyp def_id in
    rewrite (_rule_def_upper_bound $def); assumption
  ).
Local Ltac2 use_def_upper_bound_in_hyp () :=
  match! goal with
  | [ h : _ |- _ ] =>
    let def_id := Fresh.in_goal @_temp in
    enough (forall (A : R -> Prop) (M : R), is_upper_bound A M <-> _upper_bound_def_type A M) as $def_id;
    Control.focus 1 1 (fun () => 
      let def := Control.hyp def_id in
      rewrite (_rule_def_upper_bound $def) in $h;
      let h_constr := Control.hyp h in apply $h_constr
    )
  end.
#[export] Hint Extern 1 => ltac2:(use_def_upper_bound_in_goal ()) : wp_definitions.
#[export] Hint Extern 1 => ltac2:(use_def_upper_bound_in_hyp ()) : wp_definitions.
(* Tactic for expanding definition *)
Local Ltac2 exp_def_upper_bound (t : constr) :=
  lazy_match! t with
  | context [ is_upper_bound ?a ?m ] => 
    let def := get_type constr:(definition_upper_bound $a $m) in
    print (of_string "");
    print (concat (of_constr constr:(definition_upper_bound)) (of_string ":"));
    print (concat (of_string "    ") (of_constr def))
  | _ => 
    print (of_string ""); 
    print (concat (of_string "'upper bound' does not occur in ") (of_constr t))
  end.
Ltac2 Notation "Expand" "the" "definition" "of" "upper" "bound" "in" t(constr) := 
  exp_def_upper_bound t.
(* Notation *)
Notation "M 'is' 'an' '_upper' 'bound_' 'for' A" := 
  (is_upper_bound A M) (at level 69).
Notation "M 'is' 'an' 'upper' 'bound' 'for' A" := 
  (is_upper_bound A M) (at level 69, only parsing).


(** is a lower bound *)
(* Definition *)
Definition is_lower_bound (A : R -> Prop) (m : R) :=
    locked (for all a : R, A a -> m <= a).
Notation "'_lower_bound_def_type'" := 
  (fun (A : R -> Prop) (m : R) => for all a : R, A a -> m <= a) (at level 69, only parsing).
Lemma definition_lower_bound (A : R -> Prop) (M : R) : 
  is_lower_bound A M   <->   _lower_bound_def_type A M.
Proof. unfold is_lower_bound; rewrite <- lock; reflexivity. Qed.
(* Hint for using definition *)
Lemma _rule_def_lower_bound 
  (def : forall (A : R -> Prop) (M : R), 
    is_lower_bound A M <-> _lower_bound_def_type A M) :
  is_lower_bound   =   _lower_bound_def_type.
Proof.
  apply functional_extensionality; intro A.
  apply functional_extensionality; intro M.
  apply propositional_extensionality; apply def.
Qed.
Local Ltac2 use_def_lower_bound_in_goal () :=
  let def_id := Fresh.in_goal @_temp in
  enough (forall (A : R -> Prop) (M : R), is_lower_bound A M <-> _lower_bound_def_type A M) as $def_id;
  Control.focus 1 1 (fun () => 
    let def := Control.hyp def_id in
    rewrite (_rule_def_lower_bound $def); assumption
  ).
Local Ltac2 use_def_lower_bound_in_hyp () :=
  match! goal with
  | [ h : _ |- _ ] =>
    let def_id := Fresh.in_goal @_temp in
    enough (forall (A : R -> Prop) (M : R), is_lower_bound A M <-> _lower_bound_def_type A M) as $def_id;
    Control.focus 1 1 (fun () => 
      let def := Control.hyp def_id in
      rewrite (_rule_def_lower_bound $def) in $h;
      let h_constr := Control.hyp h in apply $h_constr
    )
  end.
#[export] Hint Extern 1 => ltac2:(use_def_lower_bound_in_goal ()) : wp_definitions.
#[export] Hint Extern 1 => ltac2:(use_def_lower_bound_in_hyp ()) : wp_definitions.
(* Tactic for expanding definition *)
Local Ltac2 exp_def_lower_bound (t : constr) :=
  lazy_match! t with
  | context [ is_lower_bound ?a ?m ] => 
    let def := get_type constr:(definition_lower_bound $a $m) in
    print (of_string "");
    print (concat (of_constr constr:(definition_lower_bound)) (of_string ":"));
    print (concat (of_string "    ") (of_constr def))
  | _ => 
    print (of_string ""); 
    print (concat (of_string "'lower bound' does not occur in ") (of_constr t))
  end.
Ltac2 Notation "Expand" "the" "definition" "of" "lower" "bound" "in" t(constr) := 
  exp_def_lower_bound t.
(* Notation *)
Notation "m 'is' 'a' '_lower' 'bound_' 'for' A" := 
  (is_lower_bound A m) (at level 69).
Notation "m 'is' 'a' 'lower' 'bound' 'for' A" := 
  (is_lower_bound A m) (at level 69, only parsing).


(** is bounded above *)
(* Definition *)
Definition is_bounded_above (A : R -> Prop) :=
  locked (there exists M : ℝ, is_upper_bound A M).
Notation "'_bounded_above_def_type'" := 
  (fun (A : R -> Prop) => there exists M : ℝ, is_upper_bound A M) (at level 69, only parsing).
Lemma definition_bounded_above (A : R -> Prop) :
  is_bounded_above A   <->  _bounded_above_def_type A.
Proof. unfold is_bounded_above; rewrite <- lock; reflexivity. Qed.
(* Hint for using definition *)
Lemma _rule_def_bounded_above 
  (def : forall A : R -> Prop, is_bounded_above A <-> _bounded_above_def_type A) :
  is_bounded_above   =   _bounded_above_def_type.
Proof.
  apply functional_extensionality; intro A.
  apply propositional_extensionality. apply def.
Qed.
Local Ltac2 use_def_bounded_above_in_goal () :=
  let def_id := Fresh.in_goal @_temp in
  enough (forall A : R -> Prop, is_bounded_above A <-> _bounded_above_def_type A) as $def_id;
  Control.focus 1 1 (fun () => 
    let def := Control.hyp def_id in
    rewrite (_rule_def_bounded_above $def); assumption
  ).
Local Ltac2 use_def_bounded_above_in_hyp () :=
  match! goal with
  | [ h : _ |- _ ] =>
    let def_id := Fresh.in_goal @_temp in
    enough (forall A : R -> Prop, is_bounded_above A <-> _bounded_above_def_type A) as $def_id;
    Control.focus 1 1 (fun () => 
      let def := Control.hyp def_id in
      rewrite (_rule_def_bounded_above $def) in $h;
      let h_constr := Control.hyp h in apply $h_constr
    )
  end.
#[export] Hint Extern 1 => ltac2:(use_def_bounded_above_in_goal ()) : wp_definitions.
#[export] Hint Extern 1 => ltac2:(use_def_bounded_above_in_hyp ()) : wp_definitions.
(* Tactic for expanding definition *)
Local Ltac2 exp_def_bounded_above (t : constr) :=
  lazy_match! t with
  | context [ is_bounded_above ?a ] => 
    let def := get_type constr:(definition_bounded_above $a) in
    print (of_string "");
    print (concat (of_constr constr:(definition_bounded_above)) (of_string ":"));
    print (concat (of_string "    ") (of_constr def))
  | _ => 
    print (of_string ""); 
    print (concat (of_string "'bounded from above' does not occur in ")
          (of_constr t))
  end.
Ltac2 Notation "Expand" "the" "definition" "of" "bounded" "from" "above" "in" t(constr) := 
  exp_def_bounded_above t.
(* Notation *)
Notation "A 'is' '_bounded' 'from' 'above_'" := (is_bounded_above A) (at level 69).
Notation "A 'is' 'bounded' 'from' 'above'" := 
  (is_bounded_above A) (at level 69, only parsing).
  

(** is bounded below *)
(* Definition *)
Definition is_bounded_below (A : R -> Prop) :=
  locked (there exists m : ℝ, is_lower_bound A m).
Notation "'_bounded_below_def_type'" := 
  (fun (A : R -> Prop) => there exists m : ℝ, is_lower_bound A m) (at level 69, only parsing).
Lemma definition_bounded_below (A : R -> Prop) :
  is_bounded_below A   <->  _bounded_below_def_type A.
Proof. unfold is_bounded_below; rewrite <- lock; reflexivity. Qed.
(* Hint for using definition *)
Lemma _rule_def_bounded_below 
  (def : forall A : R -> Prop, is_bounded_below A <-> _bounded_below_def_type A) :
  is_bounded_below   =   _bounded_below_def_type.
Proof.
  apply functional_extensionality; intro A.
  apply propositional_extensionality. apply def.
Qed.
Local Ltac2 use_def_bounded_below_in_goal () :=
  let def_id := Fresh.in_goal @_temp in
  enough (forall A : R -> Prop, is_bounded_below A <-> _bounded_below_def_type A) as $def_id;
  Control.focus 1 1 (fun () => 
    let def := Control.hyp def_id in
    rewrite (_rule_def_bounded_below $def); assumption
  ).
Local Ltac2 use_def_bounded_below_in_hyp () :=
  match! goal with
  | [ h : _ |- _ ] =>
    let def_id := Fresh.in_goal @_temp in
    enough (forall A : R -> Prop, is_bounded_below A <-> _bounded_below_def_type A) as $def_id;
    Control.focus 1 1 (fun () => 
      let def := Control.hyp def_id in
      rewrite (_rule_def_bounded_below $def) in $h;
      let h_constr := Control.hyp h in apply $h_constr
    )
  end.
#[export] Hint Extern 1 => ltac2:(use_def_bounded_below_in_goal ()) : wp_definitions.
#[export] Hint Extern 1 => ltac2:(use_def_bounded_below_in_hyp ()) : wp_definitions.
(* Tactic for expanding definition *)
Local Ltac2 exp_def_bounded_below (t : constr) :=
  lazy_match! t with
  | context [ is_bounded_below ?a ] => 
    let def := get_type constr:(definition_bounded_below $a) in
    print (of_string "");
    print (concat (of_constr constr:(definition_bounded_below)) (of_string ":"));
    print (concat (of_string "    ") (of_constr def))
  | _ => 
    print (of_string ""); 
    print (concat (of_string "'bounded from below' does not occur in ")
          (of_constr t))
  end.
Ltac2 Notation "Expand" "the" "definition" "of" "bounded" "from" "below" "in" t(constr) := 
  exp_def_bounded_below t.
(* Notation *)
Notation "A 'is' '_bounded' 'from' 'below_'" := (is_bounded_below A) (at level 69).
Notation "A 'is' 'bounded' 'from' 'below'" := 
  (is_bounded_below A) (at level 69, only parsing).


(** Definitions, notations and alternative characterizations for supremum and infimum. *)

(** Definition of supremum. *)

Definition sup (A : R -> Prop) := locked (
  match excluded_middle_informative (exists x : R, A x) with
  | Specif.right _ => 0
  | Specif.left HA1 => 
    match excluded_middle_informative (bound A) with
    | Specif.right _ => 0
    | Specif.left HA2 => proj1_sig(_, _, completeness A HA2 HA1)
    end
  end
).
Notation "'_sup_def_type'" := 
  (fun (A : R -> Prop) (M : R) => 
    M is an upper bound for A
    ∧ (for all L : ℝ, L is an upper bound for A ⇨ M ≤ L)) (at level 69, only parsing).

Lemma definition_supremum (A : R -> Prop) 
  (H1A : A is non-empty) (H2A : A is bounded from above) (M : R) :
  sup A = M   ⇔   _sup_def_type A M.
Proof.
  pose definition_non_empty as _def1;
  pose definition_upper_bound as _def2;
  pose definition_bounded_above as _def3.
  unfold sup; rewrite <- lock.
  destruct (excluded_middle_informative (exists x : R, A x)) 
    as [A_nonempty | not_A_nonempty].
  - destruct (excluded_middle_informative (bound A)) as [A_bound | not_A_bound].
    + Define M' := (proj1_sig(_, _, completeness A A_bound A_nonempty)).
      Define HypM' := (proj2_sig(_, _, completeness A A_bound A_nonempty)).
      By HypM' it holds that 
        (M' is an upper bound for A 
          ∧ (for all L : ℝ, L is an upper bound for A ⇨ M' ≤ L)).
      split.
      * Assume that (M' = M) (i); rewrite <- i.
        We conclude that
          (M' is an upper bound for A 
            ∧ (for all L : ℝ, L is an upper bound for A ⇨ M' ≤ L)).
      * Assume that (M is an upper bound for A 
          ∧ (for all L : ℝ, L is an upper bound for A ⇨ M ≤ L)).
        Since (M is an upper bound for A) it holds that (M' <= M).
        Since (M' is an upper bound for A) it holds that (M <= M').
        We conclude that (M' = M).
    + By (not_A_bound) it holds that
        (¬ (there exists M : ℝ, M is an upper bound for A)).
      clear _def3.
      Contradiction.
  - clear _def1.
    By definition_non_empty it holds that (there exists x : ℝ, A x).
    Contradiction.
Qed.

Notation "'sup' A" := (sup A) (at level 10) : R_scope. (* force not using parentheses *)

(* Hints for using definition. *)
Lemma _rule_def_supremum 
  (A : R -> Prop) (M : R)
  (def : sup A = M <-> _sup_def_type A M) : 
  (sup A = M)   =   _sup_def_type A M.
Proof. apply propositional_extensionality; apply def; assumption. Qed.
Local Ltac2 use_def_sup_in_goal () :=
  lazy_match! goal with 
  | [ |- ?m = sup ?a] => symmetry
  | [ |- _ ] => ()
  end;
  lazy_match! goal with 
  | [ |- sup ?a = ?m] =>
    let def_id := Fresh.in_goal @_temp in
    enough ((sup $a = $m) <-> _sup_def_type $a $m) as $def_id;
    Control.focus 1 1 (fun () => 
      let def := Control.hyp def_id in
      rewrite (_rule_def_supremum $a $m $def); assumption
    )
  end.

Local Ltac2 use_def_sup_in_hyp () :=
  match! goal with
  | [ h : sup ?a = ?m |- _ ] =>
    let def_id := Fresh.in_goal @_temp in
    enough ((sup $a = $m) <-> _sup_def_type $a $m) as $def_id;
    Control.focus 1 1 (fun () => 
      let def := Control.hyp def_id in
      rewrite (_rule_def_supremum $a $m $def) in $h;
      let h_constr := Control.hyp h in apply $h_constr
    )
  | [ h : ?m = ?a |- _ ] =>
    symmetry in $h;
    let def_id := Fresh.in_goal @_temp in
    enough ((sup $a = $m) <-> _sup_def_type $a $m) as $def_id;
    Control.focus 1 1 (fun () => 
      let def := Control.hyp def_id in
      rewrite (_rule_def_supremum $a $m $def) in $h;
      let h_constr := Control.hyp h in
      apply $h_constr
    )
  end.

#[export] Hint Extern 1 => ltac2:(use_def_sup_in_goal ()) : wp_definitions.
#[export] Hint Extern 1 => ltac2:(use_def_sup_in_hyp ()) : wp_definitions.


(** Alternative characterization *)
Notation "'_sup_alt_char_type'" := 
  (fun (A : R -> Prop) (M : R) => 
    M is an upper bound for A 
      ∧ (for all ε : R, ε > 0 -> 
        there exists a : R, A a ∧ a > M - ε)) (at level 69, only parsing).

Lemma alternative_characterization_supremum (A : R -> Prop) 
  (H1A : A is non-empty) (H2A : A is bounded from above) (M : R) :
  sup A = M   ⇔   _sup_alt_char_type A M.
Proof.
  pose definition_non_empty as _def1;
  pose definition_upper_bound as _def2;
  pose definition_bounded_above as _def3.
  split.
  - Assume that (sup A = M).
    split.
    + By definition_supremum we conclude that 
        (M is an upper bound for A).
    + Take ε : R. Assume that (ε > 0).
      We argue by contradiction. Assume that  
        (¬ there exists a : R, A a ∧ a > M - ε).
      It holds that (forall a : R, A a -> a <= M - ε).
      By definition_supremum it holds that
        (for all L : R, L is an upper bound for A -> M <= L) (i).
      It holds that ((M - ε) is an upper bound for A).
      By (i) it holds that (M <= M - ε).
      It holds that (ε <= 0). ↯.
  - Assume that (M is an upper bound for A
      ∧ (for all ε : R, ε > 0 -> there exists a : R, A a ∧ a > M - ε)).
    Time By definition_supremum it suffices to show that 
      (M is an upper bound for A
        ∧ (for all L : ℝ, L is an upper bound for A ⇨ M ≤ L)).
    split.
    + We conclude that (M is an upper bound for A).
    + Take L : R. Assume that (L is an upper bound for A).
      We argue by contradiction. Assume that (¬ M ≤ L).
      It holds that (L < M).
      Define ε := (M - L). It holds that (ε > 0).
      It holds that (there exists a : R, A a ∧ a > M - (M - L)).
      It holds that (there exists a : R, A a ∧ a > L).
      It holds that (¬ (for all a : R, A a -> a <= L)).
      It holds that (¬ L is an upper bound for A). ↯.
Qed.

(* Hints for using alternative characterization. *)
Lemma _rule_alt_char_supremum 
  (A : R -> Prop) (M : R)
  (char : sup A = M ⇔ _sup_alt_char_type A M) :
  (sup A = M)   =   (_sup_alt_char_type A M).
Proof. apply propositional_extensionality; apply char; assumption. Qed.
Local Ltac2 use_alt_char_sup_in_goal () :=
  lazy_match! goal with 
  | [ |- ?m = sup ?a] => symmetry
  | [ |- _ ] => ()
  end;
  lazy_match! goal with 
  | [ |- sup ?a = ?m] =>
    let alt_char_id := Fresh.in_goal @_temp in
    enough ((sup $a = $m) <-> _sup_alt_char_type $a $m) as $alt_char_id;
    Control.focus 1 1 (fun () => 
      let alt_char := Control.hyp alt_char_id in
      rewrite (_rule_alt_char_supremum $a $m $alt_char); assumption
    )
  end.

Local Ltac2 use_alt_char_sup_in_hyp () :=
  match! goal with
  | [ h : sup ?a = ?m |- _ ] =>
    let alt_char_id := Fresh.in_goal @_temp in
    enough ((sup $a = $m) <-> _sup_alt_char_type $a $m) as $alt_char_id;
    Control.focus 1 1 (fun () => 
      let alt_char := Control.hyp alt_char_id in
      rewrite (_rule_alt_char_supremum $a $m $alt_char) in $h;
      let h_constr := Control.hyp h in apply $h_constr
    )
  | [ h : ?m = ?a |- _ ] =>
    symmetry in $h;
    let alt_char_id := Fresh.in_goal @_temp in
    enough ((sup $a = $m) <-> _sup_alt_char_type $a $m) as $alt_char_id;
    Control.focus 1 1 (fun () => 
      let alt_char := Control.hyp alt_char_id in
      rewrite (_rule_alt_char_supremum $a $m $alt_char) in $h;
      let h_constr := Control.hyp h in apply $h_constr
    )
  end.

#[export] Hint Extern 1 => ltac2:(use_alt_char_sup_in_goal ()) : wp_definitions.
#[export] Hint Extern 1 => ltac2:(use_alt_char_sup_in_hyp ()) : wp_definitions.

(* Tactic for expanding definition *)
Local Ltac2 exp_def_supremum (t : constr) :=
  let print_info (def_w_hyps : constr) (alt_w_hyps : constr) :=
    lazy_match! def_w_hyps with
    | ?h1 -> ?h2 -> ?def =>
      lazy_match! alt_w_hyps with
      | _ -> _ -> ?alt_char =>
        print (of_string "");
        print (concat_list ((of_string "Given that ") :: (of_constr h1)
                              :: (of_string " and ") :: (of_constr h2) 
                              :: (of_string ":") :: []));
        print (concat (of_constr constr:(definition_supremum)) (of_string ":"));
        print (concat (of_string "    ") (of_constr def));
        print (concat (of_constr constr:(alternative_characterization_supremum))
                      (of_string ":"));
        print (concat (of_string "    ") (of_constr alt_char))
      end
    end
  in
  lazy_match! t with
  | context [ sup ?a = ?m ] => 
    let def_with_hyps := get_type 
      constr:(fun (h1 : $a is non-empty) (h2 : $a is bounded from above) =>
        definition_supremum $a h1 h2 $m) in
    let alt_char_with_hyps := get_type
      constr:(fun (h1 : $a is non-empty) (h2 : $a is bounded from above) =>
        alternative_characterization_supremum $a h1 h2 $m) in
    print_info def_with_hyps alt_char_with_hyps
  | context [ ?m = sup ?a ] =>
    let def_with_hyps := get_type 
      constr:(fun (h1 : $a is non-empty) (h2 : $a is bounded from above) =>
        definition_supremum $a h1 h2 $m) in
    let alt_char_with_hyps := get_type
      constr:(fun (h1 : $a is non-empty) (h2 : $a is bounded from above) =>
        alternative_characterization_supremum $a h1 h2 $m) in
    print_info def_with_hyps alt_char_with_hyps  
  | context [ sup ?a ] => 
    let def_with_hyps := get_type constr:(definition_supremum $a) in
    let alt_char_with_hyps := get_type 
      constr:(alternative_characterization_supremum $a) in
    print_info def_with_hyps alt_char_with_hyps
  | _ => 
    print (of_string ""); 
    print (concat (of_string "'sup' does not occur in ")
          (of_constr t))
  end.
Ltac2 Notation "Expand" "the" "definition" "of" "supremum" "in" t(constr) := 
  exp_def_supremum t.
Ltac2 Notation "Expand" "the" "definition" "of" "sup" "in" t(constr) := 
  exp_def_supremum t.


(** Definition of infimum. *)

Local Definition _opp (A : R -> Prop) (x : R) := A (-x).

Definition inf (A : R -> Prop) := 
  locked (- sup (_opp A)).

(* Preparation for definition inifimum. *)

Lemma _prop1_opp (A : R -> Prop) (a : R) :
  A a -> _opp A (-a).
Proof.
  Assume that (A a).
  It suffices to show that (A (--a)).
  It holds that (--a = a).
  Since (--a = a) we conclude that (A (--a)).
Qed.

Lemma _nonempty_implies_min_nonempty (A : R -> Prop) :
  A is non-empty -> _opp A is non-empty.
Proof.
  pose definition_non_empty as _def.
  Assume that (A is non-empty). 
  It holds that (there exists a : R, A a).
  Obtain such an a. 
  It suffices to show that (there exists b : R, _opp A b).
  Choose b := (-a). 
  By _prop1_opp we conclude that (_opp A b).
Qed.

Lemma _bdd_below_implies_min_bdd_above (A : R -> Prop) :
  A is bounded from below -> _opp A is bounded from above.
Proof.
  pose definition_bounded_above as _def1;
  pose definition_bounded_below as _def2;
  pose definition_upper_bound as _def3;
  pose definition_lower_bound as _def4.
  Assume that (A is bounded from below).
  It holds that 
    (there exists l : R, l is a lower bound for A).
  Obtain such an l.
  It holds that (l is a lower bound for A) (i).
  It suffices to show that 
    (there exists L : R, L is an upper bound for _opp A).
  Choose L := (-l). 
  It suffices to show that 
    (forall b : R, _opp A b -> b <= L).
  Take b : R. Assume that (_opp A b).
  It holds that (A (-b)).
  By (i) it holds that (l <= -b).
  We conclude that (& b <= -l = L).
Qed.

Notation "'_inf_def_type'" := 
  (fun (A : R -> Prop) (m : R) => 
    m is a lower bound for A
      ∧ (for all l : ℝ, l is a lower bound for A ⇨ l ≤ m)) (at level 69, only parsing).

Lemma definition_infimum (A : R -> Prop) (H1A : A is non-empty)
  (H2A : A is bounded from below) (m : R) :
  inf A = m   ⇔   _inf_def_type A m.
Proof.
  pose definition_bounded_above as _def1;
  pose definition_bounded_below as _def2;
  pose definition_upper_bound as _def3;
  pose definition_lower_bound as _def4.

  unfold inf; rewrite <- lock.
  By _nonempty_implies_min_nonempty it holds that (_opp A is non-empty).
  By _bdd_below_implies_min_bdd_above it holds that (_opp A is bounded from above).
  (* ... so sup -A is well-defined. *)
  split.
  - Assume that (- sup (_opp A) = m).
    It holds that (sup (_opp A) = -m).
    By definition_supremum it holds that
      (-m is an upper bound for _opp A
        ∧ (for all L : ℝ, L is an upper bound for _opp A ⇨ -m ≤ L)).
    split.
    + It suffices to show that
        (for all a : R, A a -> m <= a).
      Take a : R. Assume that (A a).
      By _prop1_opp it holds that (_opp A (-a)).
      Since (-m is an upper bound for _opp A) it holds that (-a <= -m).
      We conclude that (m <= a).
    + Take l : R. Assume that (l is a lower bound for A).
      We claim that (-l is an upper bound for _opp A).
      { It suffices to show that
          (for all b : R, _opp A b -> b <= -l).
        Take b : R. Assume that (_opp A b).
        Since (l is a lower bound for A) it holds that (l <= -b).
        We conclude that (b <= -l).
      }
      Since (for all L : ℝ, L is an upper bound for _opp A ⇨ -m ≤ L)
        it holds that (-m <= -l).
      We conclude that (l <= m).
  - Assume that (m is a lower bound for A
      ∧ (for all l : ℝ, l is a lower bound for A ⇨ l <= m)).
    It suffices to show that (sup (_opp A) = -m).
    By definition_supremum it suffices to show that
      (-m is an upper bound for _opp A
        ∧ (for all L : ℝ, L is an upper bound for _opp A ⇨ -m ≤ L)).
    split.
    + It suffices to show that 
        (for all b : R, _opp A b -> b <= -m).
      Take b : R. Assume that (_opp A b).
      It holds that (A (-b)).
      Since (m is a lower bound for A) it holds that (m <= -b).
      We conclude that (b <= -m).
    + Take L : R. Assume that (L is an upper bound for _opp A).
      We claim that (-L is a lower bound for A).
      { It suffices to show that 
          (for all a : R, A a -> -L <= a).
        Take a : R. Assume that (A a).
        By _prop1_opp it holds that (_opp A (-a)).
        Since (L is an upper bound for _opp A) it holds that (-a <= L).
        We conclude that (-L <= a).
      }
      Since (for all l : ℝ, l is a lower bound for A ⇨ l <= m)
        it holds that (-L <= m).
      We conclude that (-m <= L).
  Qed.

Notation "'inf' A" := (inf A) (at level 10) : R_scope. (* force not using parentheses *)
 
(* Hints for using definition. *)
Lemma _rule_def_infimum 
  (A : R -> Prop) (m : R)
  (def : inf A = m <-> _inf_def_type A m) : 
  (inf A = m)   =   _inf_def_type A m.
Proof. apply propositional_extensionality; apply def; assumption. Qed.
Local Ltac2 use_def_inf_in_goal () :=
  lazy_match! goal with 
  | [ |- ?m = inf ?a] => symmetry
  | [ |- _ ] => ()
  end;
  lazy_match! goal with 
  | [ |- inf ?a = ?m] =>
    let def_id := Fresh.in_goal @_temp in
    enough ((inf $a = $m) <-> _inf_def_type $a $m) as $def_id;
    Control.focus 1 1 (fun () => 
      let def := Control.hyp def_id in
      rewrite (_rule_def_infimum $a $m $def); assumption
    )
  end.

Local Ltac2 use_def_inf_in_hyp () :=
  match! goal with
  | [ h : inf ?a = ?m |- _ ] =>
    let def_id := Fresh.in_goal @_temp in
    enough ((inf $a = $m) <-> _inf_def_type $a $m) as $def_id;
    Control.focus 1 1 (fun () => 
      let def := Control.hyp def_id in
      rewrite (_rule_def_infimum $a $m $def) in $h;
      let h_constr := Control.hyp h in apply $h_constr
    )
  | [ h : ?m = ?a |- _ ] =>
    symmetry in $h;
    let def_id := Fresh.in_goal @_temp in
    enough ((inf $a = $m) <-> _inf_def_type $a $m) as $def_id;
    Control.focus 1 1 (fun () => 
      let def := Control.hyp def_id in
      rewrite (_rule_def_infimum $a $m $def) in $h;
      let h_constr := Control.hyp h in
      apply $h_constr
    )
  end.

#[export] Hint Extern 1 => ltac2:(use_def_inf_in_goal ()) : wp_definitions.
#[export] Hint Extern 1 => ltac2:(use_def_inf_in_hyp ()) : wp_definitions.

Notation "'_inf_alt_char_type'" := 
  (fun (A : R -> Prop) (m : R) => 
    m is a lower bound for A 
      ∧ (for all ε : R, ε > 0 -> 
        there exists a : R, A a ∧ a < m + ε)) (at level 69, only parsing).

Lemma alternative_characterization_infimum (A : R -> Prop) 
  (H1A : A is non-empty) (H2A : A is bounded from below) (m : R) :
  inf A = m   ⇔   _inf_alt_char_type A m.
Proof.
  pose definition_non_empty as _def1;
  pose definition_lower_bound as _def2;
  pose definition_bounded_below as _def3.
  split.
  - Assume that (inf A = m).
    split.
    + By definition_infimum we conclude that 
        (m is a lower bound for A).
    + Take ε : R. Assume that (ε > 0).
      We argue by contradiction. Assume that  
        (¬ there exists a : R, A a ∧ a < m + ε).
      It holds that (forall a : R, A a -> a >= m + ε).
      By definition_infimum it holds that
        (for all l : R, l is a lower bound for A -> l <= m) (i).
      It holds that ((m + ε) is a lower bound for A).
      By (i) it holds that (m + ε <= m).
      It holds that (ε <= 0). ↯.
  - Assume that (m is a lower bound for A
      ∧ (for all ε : R, ε > 0 -> there exists a : R, A a ∧ a < m + ε)).
    By definition_infimum it suffices to show that 
      (m is a lower bound for A
        ∧ (for all l : ℝ, l is a lower bound for A ⇨ l ≤ m)).
    split.
    + We conclude that (m is a lower bound for A).
    + Take l : R. Assume that (l is a lower bound for A).
      We argue by contradiction. Assume that (¬ l ≤ m).
      It holds that (l > m).
      Define ε := (l - m). It holds that (ε > 0).
      It holds that (there exists a : R, A a ∧ a < m + (l - m)) (i).
      It holds that (there exists a : R, A a ∧ a < l).
      It holds that (¬ (for all a : R, A a -> l <= a)).
      It holds that (¬ l is a lower bound for A). ↯.
Qed.

Lemma _rule_alt_char_infimum
  (A : R -> Prop) (m : R)
  (char : inf A = m ⇔ 
    m is a lower bound for A ∧ (for all ε : R, ε > 0 -> there exists a : R, A a ∧ a < m + ε)) :
  (inf A = m)   =   (m is a lower bound for A 
                      ∧ (for all ε : R, ε > 0 -> there exists a : R, A a ∧ a < m + ε)).
Proof. apply propositional_extensionality; apply char; assumption. Qed.
#[export] Hint Extern 2 => (match goal with 
                            | |- inf ?a = ?m => rewrite (_rule_alt_char_infimum a m)
                            | |- ?m = inf ?a => symmetry; rewrite (_rule_alt_char_infimum a m)
                            end) : wp_definitions.
#[export] Hint Extern 2 => (match goal with 
                            | h : inf ?a = ?m |- _ => rewrite (_rule_alt_char_infimum a m) in h
                            | h : ?m = inf ?a |- _ => symmetry in h; rewrite (_rule_alt_char_infimum a m) in h
                            end) : wp_definitions.
(* Tactic for expanding definition *)
Local Ltac2 exp_def_infimum (t : constr) :=
  let print_info (def_w_hyps : constr) (alt_w_hyps : constr) :=
    lazy_match! def_w_hyps with
    | ?h1 -> ?h2 -> ?def =>
      lazy_match! alt_w_hyps with
      | _ -> _ -> ?alt_char =>
        print (of_string "");
        print (concat_list ((of_string "Given that ") :: (of_constr h1)
                              :: (of_string " and ") :: (of_constr h2) 
                              :: (of_string ":") :: []));
        print (concat (of_constr constr:(definition_infimum)) (of_string ":"));
        print (concat (of_string "    ") (of_constr def));
        print (concat (of_constr constr:(alternative_characterization_infimum))
                      (of_string ":"));
        print (concat (of_string "    ") (of_constr alt_char))
      end
    end
  in
  lazy_match! t with
  | context [ inf ?a = ?m ] => 
    let def_with_hyps := get_type 
      constr:(fun (h1 : $a is non-empty) (h2 : $a is bounded from below) =>
        definition_infimum $a h1 h2 $m) in
    let alt_char_with_hyps := get_type
      constr:(fun (h1 : $a is non-empty) (h2 : $a is bounded from below) =>
        alternative_characterization_infimum $a h1 h2 $m) in
    print_info def_with_hyps alt_char_with_hyps
  | context [ ?m = inf ?a ] =>
    let def_with_hyps := get_type 
      constr:(fun (h1 : $a is non-empty) (h2 : $a is bounded from below) =>
        definition_infimum $a h1 h2 $m) in
    let alt_char_with_hyps := get_type
      constr:(fun (h1 : $a is non-empty) (h2 : $a is bounded from below) =>
        alternative_characterization_infimum $a h1 h2 $m) in
    print_info def_with_hyps alt_char_with_hyps  
  | context [ inf ?a ] => 
    let def_with_hyps := get_type constr:(definition_infimum $a) in
    let alt_char_with_hyps := get_type 
      constr:(alternative_characterization_infimum $a) in
    print_info def_with_hyps alt_char_with_hyps
  | _ => 
    print (of_string ""); 
    print (concat (of_string "'inf' does not occur in ")
          (of_constr t))
  end.
Ltac2 Notation "Expand" "the" "definition" "of" "infimum" "in" t(constr) := 
  exp_def_infimum t.
Ltac2 Notation "Expand" "the" "definition" "of" "inf" "in" t(constr) := 
  exp_def_infimum t.



(** 'sup' and 'inf' satisfy their defining properties. *)

Lemma _sup_is_upper_bound (A : R -> Prop)
  (def : forall (M : R),
    sup A = M   ⇔   M is an upper bound for A
                      ∧ (for all L : ℝ, L is an upper bound for A ⇨ M ≤ L)) :
  sup A is an upper bound for A.
Proof.
  apply def; reflexivity.
Qed.
  
Lemma _sup_is_least_upper_bound (A : R -> Prop)
  (def : forall (M : R),
    sup A = M   ⇔   M is an upper bound for A
                      ∧ (for all L : ℝ, L is an upper bound for A ⇨ M ≤ L)) :
  forall L : R, L is an upper bound for A -> sup A <= L.
Proof.
  apply def; reflexivity.
Qed.

Lemma _sup_is_approximated (A : R -> Prop)
  (char : forall M : R,
    sup A = M   ⇔   M is an upper bound for A 
                      ∧ (for all ε : R, ε > 0 -> 
                        there exists a : R, A a ∧ a > M - ε)) :
  for all ε : R, ε > 0 -> 
    there exists a : R, A a ∧ 
      a > sup A - ε.
Proof.
  apply char; reflexivity.
Qed.


Lemma _inf_is_lower_bound (A : R -> Prop)
  (def : forall m : R,
    inf A = m   ⇔   m is a lower bound for A
                      ∧ (for all l : ℝ, l is a lower bound for A ⇨ l ≤ m)) :
  inf A is a lower bound for A.
Proof.
  apply def; reflexivity.
Qed.

Lemma _inf_is_largest_lower_bound (A : R -> Prop)
  (def : forall m : R,
    inf A = m   ⇔   m is a lower bound for A
                    ∧ (for all l : ℝ, l is a lower bound for A ⇨ l ≤ m)) :
  forall l : R, l is a lower bound for A -> l <= inf A.
Proof.
  apply def; reflexivity.
Qed.

Lemma _inf_is_approximated (A : R -> Prop)
  (char : for all m : R,
    inf A = m   ⇔   m is a lower bound for A 
                      ∧ (for all ε : R, ε > 0 -> 
                        there exists a : R, A a ∧ a < m + ε)) :
  for all ε : R, ε > 0 -> 
    there exists a : R, A a ∧
      a < inf A + ε.
Proof.
  apply char; reflexivity.
Qed.


#[export] Hint Resolve _sup_is_upper_bound : wp_definitions.
#[export] Hint Resolve _sup_is_least_upper_bound : wp_definitions.
#[export] Hint Resolve _sup_is_approximated : wp_definitions.

#[export] Hint Resolve _inf_is_lower_bound : wp_definitions.
#[export] Hint Resolve _inf_is_largest_lower_bound : wp_definitions.
#[export] Hint Resolve _inf_is_approximated : wp_definitions.


(** Advanced lemmas *)
(* Use that sup A is an upper bound for A,
  skips explicit unfolding of def upper bound *)
Lemma _sup_behaves_as_bound (A : R -> Prop) (a : R)
  (def : for all M : R, sup A = M 
          <-> M is an upper bound for A
          ∧ (for all L : ℝ, L is an upper bound for A ⇨ M ≤ L)) :
  (A a) -> a <= sup A.
Proof.
  intros.
  assert (sup A is an upper bound for A) as H1 by apply def; reflexivity.
  rewrite _rule_def_upper_bound in H1.
  apply H1.
  - assumption.
  - apply definition_upper_bound.
Qed.

(* Use that inf A is a lower bound for A,
  skips explicit unfolding of def lower bound *)
  Lemma _inf_behaves_as_bound (A : R -> Prop) (a : R)
  (def : for all m : R, inf A = m 
          <-> m is a lower bound for A
          ∧ (for all l : ℝ, l is a lower bound for A ⇨ l ≤ m)) :
  (A a) -> inf A <= a.
Proof.
  intros.
  assert (inf A is a lower bound for A) as H1 by apply def; reflexivity.
  rewrite _rule_def_lower_bound in H1.
  apply H1.
  - assumption.
  - apply definition_lower_bound.
Qed.



(* *** OLD STUFF (below) *** *)



(* Lemma max_or_strict :
  ∀ (A : ℝ → Prop) (M : ℝ),
    is_sup A M ⇒ 
      (A M) ∨ (∀ a : ℝ, (A a) ⇒ a < M).
Proof.
    Take A : (ℝ → Prop).
    Take M : ℝ.
    Assume that (is_sup A M).
    We argue by contradiction.
    Assume that (¬ (A M ∨ (for all a : ℝ, (A a) ⇒ a < M))).
    It holds that ((¬ (A M)) ∧ 
      ¬(∀ a : ℝ, (A a) ⇒ a < M)) (i).
    Because (i) both(¬ (A M)) and (¬(∀ a : ℝ, (A a) ⇒ a < M)) hold.
    We claim that (for all a : ℝ, (A a) ⇒ a < M).
    { 
      Take a : ℝ. Assume that (A a).
      By sup_is_upp_bd it holds that (is_upper_bound A M).
      It holds that (a ≤ M).
      We claim that (M ≠ a).
      {
        Assume that (M = a) (ii).
        We claim that (A M).
        { It holds that (A a) (iii).
          (* TODO: We conclude that (A M). should work *)
      exact (eq_ind_r(_,_,A,(iii),_,(ii))).
        }
        Contradiction.
      }
      We conclude that (a < M).
    }
    Contradiction.
Qed. *)

(** * Lemmas for convenience*)
(* Lemma bounded_by_upper_bound_propform :
  ∀ (A : ℝ → Prop) (M : ℝ) (b : ℝ),
    is_upper_bound A M ⇒ A b ⇒ b ≤ M.
Proof.
    Take A : (ℝ → Prop).
    Take M : ℝ.
    Take b : ℝ.
    Assume that (is_upper_bound A M) (i).
    Assume that (A b) (ii).
    We conclude that (b ≤ M).
Qed.

Lemma bounded_by_lower_bound_propform :
  ∀ (A : ℝ → Prop) (m : ℝ) (b : ℝ),
    is_lower_bound A m ⇒ A b ⇒ m ≤ b.
Proof.
    Take A : (ℝ → Prop).
    Take m : ℝ.
    Take b: ℝ.
    Assume that (is_lower_bound A m) (i).
    Assume that (A b) (ii).
    We conclude that (m ≤ b).
Qed. *)

Lemma any_upp_bd_ge_sup :
  ∀ A : (ℝ → Prop),
    ∀ M L : ℝ,
      is_lub A M ⇒ (Raxioms.is_upper_bound A L ⇒ M ≤ L).
Proof.
    Take A : (ℝ → Prop).
    Take M : ℝ.
    Take L : ℝ.
    Assume that (is_lub A M) (i).
    Assume that (Raxioms.is_upper_bound A L).
    unfold is_lub in i.
    It holds that (for all M0 : ℝ, Raxioms.is_upper_bound A M0 ⇨ M ≤ M0).
    We conclude that (M ≤ L).
Qed.

Lemma exists_almost_maximizer :
  ∀ (A : ℝ → Prop) (M : ℝ),
    is_lub A M ⇒
      ∀ (L : ℝ), L < M ⇒ 
        ∃ a : ℝ, (A a) ∧ L < a.
Proof.
    Take A : (ℝ → Prop).
    Take M : ℝ.
    Assume that (is_lub A M).
    Take L : ℝ.
    Assume that (L < M).
    We argue by contradiction.
    Assume that (¬ (there exists a : ℝ, (A a) ∧ L < a)) (i). 
    It holds that (∀ x : ℝ, (A x) ⇒ x <= L) (ii).
    By (ii) it holds that (Raxioms.is_upper_bound A L).
    (** TODO: why can't this be done automatically? *)
    By any_upp_bd_ge_sup it holds that (M <= L).
    It holds that (¬(M ≤ L)).
    Contradiction.
Qed.

Lemma exists_almost_maximizer_ε :
  ∀ (A : ℝ → Prop) (M : ℝ),
    is_lub A M ⇒
      ∀ (ε : ℝ), ε > 0 ⇒ 
        ∃ a : R, (A a) ∧ M - ε < a.
Proof.
    Take A : (ℝ → Prop).
    Take M : ℝ.
    Assume that (is_lub A M).
    Take ε : ℝ; such that (ε > 0).
    It holds that (M - ε < M).
    (** TODO: fix this *)
    apply exists_almost_maximizer with (L := M- ε) (M := M).
    - We conclude that (is_lub A M).
    - We conclude that (M - ε < M).
Qed.

Lemma seq_ex_almost_maximizer_ε :
  ∀ (a : ℕ → ℝ) (pr : has_ub a) (ε : ℝ), 
    ε > 0 ⇒ ∃ k : ℕ, a k > lub a pr - ε.
Proof.
    Take a : (ℕ → ℝ).
    Assume that (has_ub a) (i).
    Expand the definition of lub.
    That is, write the goal as (for all ε : ℝ,  ε > 0 
      ⇨ there exists k : ℕ, a k > (let (a0, _) := ub_to_lub a (i) in a0) - ε).
    Define lub_a_prf := (ub_to_lub a (i)).
    clear _defeq.
    Obtain such an l.
    Take ε : ℝ; such that (ε > 0).
    By exists_almost_maximizer_ε it holds that (∃ y : ℝ, (EUn a) y ∧ y > l - ε).
    Obtain such a y. It holds that ((EUn a) y ∧ y > l - ε) (ii).
    It holds that (there exists n : ℕ , y = a n).
    Obtain such an n.
    Choose k := n.
    It suffices to show that (l - ε < a n).
    We conclude that (& l - ε < y = a n).
Qed.

Lemma seq_ex_almost_maximizer_m :
  ∀ (a : ℕ → ℝ) (pr : has_ub a) (m : ℕ), 
    ∃ k : ℕ, a k > lub a pr - 1 / (INR(m) + 1).
Proof.
    Take a : (ℕ → ℝ).
    Assume that (has_ub a).
    Take m : ℕ.
    apply seq_ex_almost_maximizer_ε.
    (** We need to show that $1/(m+1) > 0$.*)
    It holds that (0 < m + 1)%R.
    We conclude that (1 / (m+1) > 0).
Qed.

Lemma exists_almost_lim_sup_aux :
  ∀ (a : ℕ → ℝ) (pr : has_ub a) (m : ℕ) (N : ℕ),
    ∃ k : ℕ, (k ≥ N)%nat ∧ a k > sequence_ub a pr N - 1 / (INR(m) + 1).
Proof.
    Take a : (ℕ → ℝ).
    Assume that (has_ub a) (i).
    Take m, Nn : ℕ.
    By seq_ex_almost_maximizer_m it holds that
      (∃ k : ℕ, a (Nn + k)%nat > sequence_ub a (i) Nn - 1 / (INR m + 1)).
    Obtain such a k.
    Choose l := (Nn+k)%nat.
    We show both statements.
    - We need to show that (l ≥ Nn)%nat.
      We conclude that (l ≥ Nn)%nat.
    - We need to show that ( a l > sequence_ub a (i) Nn - 1 / (m + 1) ).
      We conclude that ( a l > sequence_ub a (i) Nn - 1 / (m + 1) ).
Qed.

Close Scope R_scope.
