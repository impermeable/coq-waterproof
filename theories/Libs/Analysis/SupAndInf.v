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

Require Import Automation.
Require Import Notations.
Require Import Tactics.

Open Scope R_scope.

Waterproof Enable Automation RealsAndIntegers.
Waterproof Enable Automation Intuition.


(** Functions used for using and expanding definitions *)

Require Import Logic.FunctionalExtensionality.
Axiom prop_univ : forall {P Q : Prop}, (P <-> Q) -> (P = Q).

Require Import Util.Init.
Require Import Ltac2.Message.
Local Ltac2 get_type (x: constr) : constr := eval unfold type_of in (type_of $x).
Local Ltac2 concat_list (ls : message list) : message :=
  List.fold_right concat (of_string "") ls.


(** Definitions and notation for non-emptyness and boundedness. *)

(** Non-empty *)
(* Definition *)
Axiom is_non_empty : (R -> Prop) -> Prop.
Axiom definition_non_empty : forall A : R -> Prop, 
  is_non_empty A   <->   there exists x : R, A x.
Lemma _rule_def_non_empty 
  (def : forall A : R -> Prop, is_non_empty A <-> there exists x : R, A x) :
  is_non_empty   =   fun (A : R -> Prop) => there exists x : R, A x.
Proof.
  apply functional_extensionality; intro A; apply prop_univ.
  apply def.
Qed.
(* Notation *)
Notation "A 'is' '_non-empty_'" := (is_non_empty A) (at level 69).
Notation "A 'is' 'non-empty'" := (is_non_empty A) (at level 69, only parsing).
(* Hint for using definition *)
(* #[export] Hint Extern 1 => (rewrite -> _unfold_def_non_empty) : wp_reals. *)
#[export] Hint Extern 1 => (rewrite _rule_def_non_empty) : wp_reals.
#[export] Hint Extern 1 => (match goal with | h : _ |- _ => 
                              rewrite _rule_def_non_empty in h end) : wp_reals.



(* Tactic for expanding definition *)
Local Ltac2 exp_def_non_empty (t : constr) :=
  lazy_match! t with
  | context [ is_non_empty ?a ] => 
    let def := get_type constr:(definition_non_empty $a) in
    print (of_string "");
    print (concat (of_constr constr:(definition_non_empty)) (of_string ":"));
    print (concat (of_string "      ") (of_constr def))
  | _ => 
    print (of_string ""); 
    print (concat (of_string "'non-empty' does not occur in ") (of_constr t))
  end.
Ltac2 Notation "Expand" "the" "definition" "of" "non-empty" "in" t(constr) := 
  exp_def_non_empty t.

(** Test for expanding definition. *)
Goal False.
Proof.
  Expand the definition of non-empty in ([0,1] is non-empty).
  Expand the definition of non-empty in (bound [0,1]).
Abort.


(** Continuation file *)

(** is an upper bound *)
(* Definition *)
Axiom is_upper_bound : (R -> Prop) -> R -> Prop.
Axiom definition_upper_bound : forall (A : R -> Prop) (M : R), 
  is_upper_bound A M   <->   (for all a : R, A a -> a <= M).
(* Notation *)
Notation "M 'is' 'an' '_upper' 'bound_' 'for' A" := 
  (is_upper_bound A M) (at level 69).
Notation "M 'is' 'an' 'upper' 'bound' 'for' A" := 
  (is_upper_bound A M) (at level 69, only parsing).
(* Hint for using definition *)
Check fun (A : R -> Prop) (M : R) => forall a : R, A a -> a <= M.
Lemma _rule_def_upper_bound 
  (def : forall (A : R -> Prop) (M : R), 
    is_upper_bound A M <-> (for all a : R, A a -> a <= M)) :
  is_upper_bound   =   fun (A : R -> Prop) (M : R) => forall a : R, A a -> a <= M.
Proof.
  apply functional_extensionality; intro A.
  apply functional_extensionality; intro M.
  apply prop_univ; apply def.
Qed.
#[export] Hint Extern 1 => (rewrite -> _rule_def_upper_bound) : wp_reals.
#[export] Hint Extern 1 => (match goal with | h : _ |- _ => 
                              rewrite _rule_def_upper_bound in h end) : wp_reals.
(* Tactic for expanding definition *)
Local Ltac2 exp_def_upper_bound (t : constr) :=
  lazy_match! t with
  | context [ is_upper_bound ?a ?m ] => 
    let def := get_type constr:(definition_upper_bound $a $m) in
    print (of_string "");
    print (concat (of_constr constr:(definition_upper_bound)) (of_string ":"));
    print (concat (of_string "      ") (of_constr def))
  | _ => 
    print (of_string ""); 
    print (concat (of_string "'upper bound' does not occur in ") (of_constr t))
  end.
Ltac2 Notation "Expand" "the" "definition" "of" "upper" "bound" "in" t(constr) := 
  exp_def_upper_bound t.

(* small test unfolding notation *)
Goal False.
Proof. 
  Expand the definition of upper bound in (1 is an upper bound for [0,1]).
Abort.

(** is a lower bound *)
(* Definition *)
Axiom is_lower_bound : (R -> Prop) -> R -> Prop.
Axiom definition_lower_bound : forall (A : R -> Prop) (m : R), 
  is_lower_bound A m   <->   (for all a : R, A a -> m <= a).
(* Notation *)
Notation "m 'is' 'a' '_lower' 'bound_' 'for' A" := 
  (is_lower_bound A m) (at level 69).
Notation "m 'is' 'a' 'lower' 'bound' 'for' A" := 
  (is_lower_bound A m) (at level 69, only parsing).
(* Hint for using definition *)
Lemma _rule_def_lower_bound 
  (def : forall (A : R -> Prop) (m : R), 
    is_lower_bound A m <-> (for all a : R, A a -> m <= a)) :
  is_lower_bound   =   fun (A : R -> Prop) (m : R) => forall a : R, A a -> m <= a.
Proof.
  apply functional_extensionality; intro A.
  apply functional_extensionality; intro m.
  apply prop_univ; apply def.
Qed.
#[export] Hint Extern 1 => (rewrite -> _rule_def_lower_bound) : wp_reals.
#[export] Hint Extern 1 => (match goal with | h : _ |- _ => 
                              rewrite _rule_def_lower_bound in h end) : wp_reals.
(* Tactic for expanding definition *)
Local Ltac2 exp_def_lower_bound (t : constr) :=
  lazy_match! t with
  | context [ is_lower_bound ?a ?m ] => 
    let def := get_type constr:(definition_lower_bound $a $m) in
    print (of_string "");
    print (concat (of_constr constr:(definition_lower_bound)) (of_string ":"));
    print (concat (of_string "      ") (of_constr def))
  | _ => 
    print (of_string ""); 
    print (concat (of_string "'lower bound' does not occur in ") (of_constr t))
  end.
Ltac2 Notation "Expand" "the" "definition" "of" "lower" "bound" "in" t(constr) := 
  exp_def_lower_bound t.

(** is bounded above *)
(* Definition *)
Axiom is_bounded_above : (R -> Prop) -> Prop.
Axiom definition_bounded_above : forall (A : R -> Prop), 
  is_bounded_above A   <->   there exists M : ℝ, is_upper_bound A M.
(* Notation *)
Notation "A 'is' '_bounded' 'from' 'above_'" := (is_bounded_above A) (at level 69).
Notation "A 'is' 'bounded' 'from' 'above'" := 
  (is_bounded_above A) (at level 69, only parsing).
(* Hint for using definition *)
Lemma _rule_def_bounded_above 
  (def : forall (A : R -> Prop),
    is_bounded_above A <-> there exists M : ℝ, is_upper_bound A M) :
  is_bounded_above   =   fun (A : R -> Prop) => there exists M : ℝ, is_upper_bound A M.
Proof.
  apply functional_extensionality; intro A.
  apply prop_univ; apply def.
Qed.
#[export] Hint Extern 1 => (rewrite _rule_def_bounded_above) : wp_reals.
#[export] Hint Extern 1 => (match goal with | h : _ |- _ => 
                              rewrite _rule_def_bounded_above in h end) : wp_reals.
(* Tactic for expanding definition *)
Local Ltac2 exp_def_bounded_above (t : constr) :=
  lazy_match! t with
  | context [ is_bounded_above ?a ] => 
    let def := get_type constr:(definition_bounded_above $a) in
    print (of_string "");
    print (concat (of_constr constr:(definition_bounded_above)) (of_string ":"));
    print (concat (of_string "      ") (of_constr def))
  | _ => 
    print (of_string ""); 
    print (concat (of_string "'bounded from above' does not occur in ")
          (of_constr t))
  end.
Ltac2 Notation "Expand" "the" "definition" "of" "bounded" "from" "above" "in" t(constr) := 
  exp_def_bounded_above t.

(* small test unfolding notation *)
Goal False.
Proof. 
  Expand the definition of bounded from above in ([0,1] is bounded from above).
Abort.

(** is bounded below *)
(* Definition *)
Axiom is_bounded_below : (R -> Prop) -> Prop.
Axiom definition_bounded_below : forall (A : R -> Prop), 
  is_bounded_below A   <->   there exists m : ℝ, is_lower_bound A m.
(* Notation *)
Notation "A 'is' '_bounded' 'from' 'below_'" := (is_bounded_below A) (at level 69).
Notation "A 'is' 'bounded' 'from' 'below'" := 
  (is_bounded_below A) (at level 69, only parsing).
(* Hint for using definition *)
Lemma _rule_def_bounded_below 
  (def : forall (A : R -> Prop),
    is_bounded_below A <-> there exists m : ℝ, is_lower_bound A m) :
  is_bounded_below   =   fun (A : R -> Prop) => (there exists m : ℝ, is_lower_bound A m).
Proof.
  apply functional_extensionality; intro A.
  apply prop_univ; apply def.
Qed.
#[export] Hint Extern 1 => (rewrite _rule_def_bounded_below) : wp_reals.
#[export] Hint Extern 1 => (match goal with | h : _ |- _ => 
                              rewrite _rule_def_bounded_below in h end) : wp_reals.
(* Tactic for expanding definition *)
Local Ltac2 exp_def_bounded_below (t : constr) :=
  lazy_match! t with
  | context [ is_bounded_below ?a ] => 
    let def := get_type constr:(definition_bounded_below $a) in
    print (of_string "");
    print (concat (of_constr constr:(definition_bounded_below)) (of_string ":"));
    print (concat (of_string "      ") (of_constr def))
  | _ => 
    print (of_string ""); 
    print (concat (of_string "'bounded from below' does not occur in ")
          (of_constr t))
  end.
Ltac2 Notation "Expand" "the" "definition" "of" "bounded" "from" "below" "in" t(constr) := 
  exp_def_bounded_below t.

(* small test unfolding notation *)
Goal False.
Proof. 
  Expand the definition of bounded from below in ([0,1] is bounded from below).
Abort.


(** Definitions, notations and alternative characterizations for supremum and infimum. *)

(** Definition of supremum.
  Uses axiomatic approach to mimic `sup A` notation
  and to enforce explicit unfolding of definitions. *)
(* Definition *)
Axiom sup : (R -> Prop) -> R.
Notation "'sup' A" := (sup A) (at level 10) : R_scope. (* force not using parentheses *)
Axiom definition_supremum : 
  for all (A : R -> Prop) (H1A : A is non-empty) (H2A : A is bounded from above) (M : R),
  sup A = M   ⇔   M is an upper bound for A
                  ∧ (for all L : ℝ, L is an upper bound for A ⇨ M ≤ L).
Lemma alternative_characterization_supremum :
  for all (A : R -> Prop) (H1A : A is non-empty) (H2A : A is bounded from above) (M : R),
  sup A = M   ⇔   M is an upper bound for A 
                  ∧ (for all ε : R, ε > 0 -> 
                        there exists a : R, A a ∧ a > M - ε).
Proof.
  intros A H1A H2A M; split.
  - intro supA_eq_M; split.
    + apply definition_supremum; assumption.
    + Take ε : R. Assume that (ε > 0).
      We argue by contradiction. Assume that  
      (¬ there exists a : R, A a ∧ a > M - ε).
      It holds that (forall a : R, A a -> a <= M - ε).
      We claim that 
        (for all L : R, L is an upper bound for A -> sup A <= L) (i).
      { apply definition_supremum ; try assumption; reflexivity. }
      By definition_upper_bound it holds that 
        ((M - ε) is an upper bound for A).
      By (i) it holds that (& M = sup A <= M - ε).
      It holds that (ε <= 0).
      It holds that (¬ ε > 0). ↯.
- intro H. apply definition_supremum; try assumption.
  split.
  + apply H.
  + Take L : R. Assume that (L is an upper bound for A).
    We argue by contradiction. Assume that (¬ M ≤ L).
    It holds that (L < M).
    Define ε := (M - L). It holds that (ε > 0).
    It holds that (there exists a : R, A a ∧ a > M - (M - L)).
    It holds that (there exists a : R, A a ∧ a > L).
    It holds that (¬ (for all a : R, A a -> a <= L)).
    By definition_upper_bound it holds that 
      (¬ L is an upper bound for A). ↯.
Qed.
(* Hints for using definition and alternative characterization. *)
Lemma _rule_def_supremum 
  (A : R -> Prop) (M : R) (H1A : A is non-empty) (H2A : A is bounded from above) 
  (def : sup A = M <->
    M is an upper bound for A ∧ (for all L : ℝ, L is an upper bound for A ⇨ M ≤ L)) : 
  (sup A = M)   =   (M is an upper bound for A 
                      ∧ (for all L : ℝ, L is an upper bound for A ⇨ M ≤ L)).
Proof. apply prop_univ; apply def; assumption. Qed.
#[export] Hint Extern 1 => (match goal with 
                            | |- sup ?a = ?m => rewrite (_rule_def_supremum a m)
                            | |- ?m = sup ?a => symmetry; rewrite (_rule_def_supremum a m)
                            end) : wp_reals.
#[export] Hint Extern 1 => (match goal with 
                            | h : sup ?a = ?m |- _ => rewrite (_rule_def_supremum a m) in h
                            | h : ?m = sup ?a |- _ => symmetry in h; rewrite (_rule_def_supremum a m) in h
                            end) : wp_reals.
                          
Lemma _rule_alt_char_supremum 
  (A : R -> Prop) (H1A : A is non-empty) (H2A : A is bounded from above) (M : R)
  (char : sup A = M ⇔ 
    M is an upper bound for A ∧ (for all ε : R, ε > 0 -> there exists a : R, A a ∧ a > M - ε)) :
  (sup A = M)   =   (M is an upper bound for A
                      ∧ (for all ε : R, ε > 0 -> there exists a : R, A a ∧ a > M - ε)).
Proof. apply prop_univ; apply char; assumption. Qed.
#[export] Hint Extern 1 => (rewrite _rule_alt_char_supremum) : wp_reals.
#[export] Hint Extern 1 => (match goal with | h : _ |- _ => 
                              rewrite _rule_alt_char_supremum in h end) : wp_reals.
(* Tactic for expanding definition *)
Local Ltac2 exp_def_supremum (t : constr) :=
  lazy_match! t with
  | context [ sup ?a ] => 
    let def_with_constraints := get_type constr:(definition_supremum $a) in
    lazy_match! def_with_constraints with
    | ?h1 -> ?h2 -> ?def =>
      let alt_char_with_constraints := 
        get_type constr:(alternative_characterization_supremum $a) in
      lazy_match! alt_char_with_constraints with
      | _ -> _ -> ?alt_char =>
        print (of_string "");
        print (concat_list ((of_string "Given that ") :: (of_constr h1)
                              :: (of_string " and ") :: (of_constr h2) 
                              :: (of_string ":") :: []));
        print (concat (of_constr constr:(definition_supremum)) (of_string ":"));
        print (concat (of_string "      ") (of_constr def));
        print (concat (of_constr constr:(alternative_characterization_supremum))
                      (of_string ":"));
        print (concat (of_string "      ") (of_constr alt_char))
      end
    end
  | _ => 
    print (of_string ""); 
    print (concat (of_string "'sup' does not occur in ")
          (of_constr t))
  end.
Ltac2 Notation "Expand" "the" "definition" "of" "supremum" "in" t(constr) := 
  exp_def_supremum t.
Ltac2 Notation "Expand" "the" "definition" "of" "sup" "in" t(constr) := 
  exp_def_supremum t.

Goal False.
  Expand the definition of supremum in (sup [0,1]).
Abort.


(** Definition of infimum.
  Uses axiomatic approach to mimic `inf A` notation
  and to enforce explicit unfolding of definitions. *)
(* Definition *)
Axiom inf : (R -> Prop) -> R.
Notation "'inf' A" := (inf A) (at level 10) : R_scope. (* force not using parentheses *)
Axiom definition_infimum : 
  for all (A : R -> Prop) (H1A : A is non-empty) (H2A : A is bounded from below) (m : R),
  inf A = m   ⇔   m is a lower bound for A
                  ∧ (for all l : ℝ, l is a lower bound for A ⇨ l ≤ m).
Lemma alternative_characterization_infimum :
  for all (A : R -> Prop) (H1A : A is non-empty) (H2A : A is bounded from below) (m : R),
  inf A = m   ⇔   m is a lower bound for A 
                  ∧ (for all ε : R, ε > 0 -> 
                        there exists a : R, A a ∧ a < m + ε).
Proof.
  intros A H1A H2A m; split.
  - intro infA_eq_m; split.
    + apply definition_infimum; assumption.
    + Take ε : R. Assume that (ε > 0).
      We argue by contradiction. Assume that  
      (¬ there exists a : R, A a ∧ a < m + ε).
      It holds that (forall a : R, A a -> a >= m + ε).
      We claim that 
        (for all l : R, l is a lower bound for A -> l <= inf A) (i).
      { apply definition_infimum ; try assumption; reflexivity. }
      By definition_lower_bound it holds that 
        ((m + ε) is a lower bound for A).
      By (i) it holds that (& m + ε <= inf A = m).
      It holds that (ε <= 0).
      It holds that (¬ ε > 0). ↯.
- intro H. apply definition_infimum; try assumption.
  split.
  + apply H.
  + Take l : R. Assume that (l is a lower bound for A).
    We argue by contradiction. Assume that (¬ l <= m).
    It holds that (l > m).
    Define ε := (l - m). It holds that (ε > 0).
    It holds that (there exists a : R, A a ∧ a < m + (l - m)).
    It holds that (there exists a : R, A a ∧ a < l).
    It holds that (¬ (for all a : R, A a -> l <= a)).
    By definition_lower_bound it holds that 
      (¬ l is a lower bound for A). ↯.
Qed.
(* Hints for using definition and alternative characterization. *)
Lemma _rule_def_infimum
  (A : R -> Prop) (H1A : A is non-empty) (H2A : A is bounded from below) (m : R)
  (def : inf A = m ⇔ 
    m is a lower bound for A ∧ (for all l : ℝ, l is a lower bound for A ⇨ l ≤ m)) :
  (inf A = m)   =   (m is a lower bound for A 
                      ∧ (for all l : ℝ, l is a lower bound for A ⇨ l ≤ m)).
Proof. apply prop_univ; apply def; assumption. Qed.
#[export] Hint Extern 1 => (rewrite _rule_def_infimum) : wp_reals.
#[export] Hint Extern 1 => (match goal with | h : _ |- _ => 
                              rewrite _rule_def_infimum in h end) : wp_reals.
Lemma _rule_alt_char_infimum
  (A : R -> Prop) (H1A : A is non-empty) (H2A : A is bounded from below) (m : R)
  (char : inf A = m ⇔ 
    m is a lower bound for A ∧ (for all ε : R, ε > 0 -> there exists a : R, A a ∧ a < m + ε)) :
  (inf A = m)   =   (m is a lower bound for A 
                      ∧ (for all ε : R, ε > 0 -> there exists a : R, A a ∧ a < m + ε)).
Proof. apply prop_univ; apply char; assumption. Qed.
#[export] Hint Extern 1 => (rewrite _rule_alt_char_infimum) : wp_reals.
#[export] Hint Extern 1 => (match goal with | h : _ |- _ => 
                              rewrite _rule_alt_char_infimum in h end) : wp_reals.
(* Tactic for expanding definition *)
Local Ltac2 exp_def_infimum (t : constr) :=
  lazy_match! t with
  | context [ inf ?a ] => 
    let def_with_constraints := get_type constr:(definition_infimum $a) in
    lazy_match! def_with_constraints with
    | ?h1 -> ?h2 -> ?def =>
      let alt_char_with_constraints := 
        get_type constr:(alternative_characterization_infimum $a) in
      lazy_match! alt_char_with_constraints with
      | _ -> _ -> ?alt_char =>
        print (of_string "");
        print (concat_list ((of_string "Given that ") :: (of_constr h1)
                              :: (of_string " and ") :: (of_constr h2) 
                              :: (of_string ":") :: []));
        print (concat (of_constr constr:(definition_infimum)) (of_string ":"));
        print (concat (of_string "      ") (of_constr def));
        print (concat (of_constr constr:(alternative_characterization_infimum))
                      (of_string ":"));
        print (concat (of_string "      ") (of_constr alt_char))
      end
    end
  | _ => 
    print (of_string ""); 
    print (concat (of_string "'inf' does not occur in ")
          (of_constr t))
  end.
Ltac2 Notation "Expand" "the" "definition" "of" "infimum" "in" t(constr) := 
  exp_def_infimum t.
Ltac2 Notation "Expand" "the" "definition" "of" "inf" "in" t(constr) := 
  exp_def_infimum t.

Goal False.
  Expand the definition of inf in (inf [0,1]).
  Expand the definition of infimum in (sup [0,1]).
Abort.


(** 'sup' and 'inf' satisfy their defining properties. *)

Lemma _sup_is_upper_bound (A : R -> Prop) (H1A : A is non-empty)
  (H2A : A is bounded from above)
  (def : forall (M : R),
    sup A = M   ⇔   M is an upper bound for A
                      ∧ (for all L : ℝ, L is an upper bound for A ⇨ M ≤ L)) :
  sup A is an upper bound for A.
Proof.
  apply def; reflexivity.
Qed.
  
Lemma _sup_is_least_upper_bound (A : R -> Prop) 
  (H1A : A is non-empty) (H2A : A is bounded from above)
  (def : forall (M : R),
    sup A = M   ⇔   M is an upper bound for A
                      ∧ (for all L : ℝ, L is an upper bound for A ⇨ M ≤ L)) :
  forall L : R, L is an upper bound for A -> sup A <= L.
Proof.
  apply def; reflexivity.
Qed.

Lemma _sup_is_approximated (A : R -> Prop) 
  (H1A : A is non-empty) (H2A : A is bounded from above) 
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


Lemma _inf_is_lower_bound (A : R -> Prop) (H1A : A is non-empty)
  (H2A : A is bounded from below)
  (def : forall m : R,
    inf A = m   ⇔   m is a lower bound for A
                      ∧ (for all l : ℝ, l is a lower bound for A ⇨ l ≤ m)) :
  inf A is a lower bound for A.
Proof.
  apply def; reflexivity.
Qed.

Lemma _inf_is_largest_lower_bound (A : R -> Prop) 
  (H1A : A is non-empty) (H2A : A is bounded from below) 
  (def : forall m : R,
    inf A = m   ⇔   m is a lower bound for A
                    ∧ (for all l : ℝ, l is a lower bound for A ⇨ l ≤ m)) :
  forall l : R, l is a lower bound for A -> l <= inf A.
Proof.
  apply def; reflexivity.
Qed.

Lemma _inf_is_approximated (A : R -> Prop) 
  (H1A : A is non-empty) (H2A : A is bounded from below) 
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


#[export] Hint Resolve _sup_is_upper_bound : wp_reals.
Goal False.
Proof.
  We claim that ([0,1] is non-empty). { admit. }
  We claim that ([0,1] is bounded from above). { admit. }
  By definition_supremum it holds that (sup [0,1] is an upper bound for [0,1]).
Abort.
#[export] Hint Resolve _sup_is_least_upper_bound : wp_reals.
#[export] Hint Resolve _sup_is_approximated : wp_reals.

#[export] Hint Resolve _inf_is_lower_bound : wp_reals.
#[export] Hint Resolve _inf_is_largest_lower_bound : wp_reals.
#[export] Hint Resolve _inf_is_approximated : wp_reals.


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


Section ConsistencyResults.

  (** Consistency results.
    Serve as sanity checks, but are not interesting for students. *)

  Context (A : R -> Prop).

  #[local] Hint Resolve definition_non_empty : wp_reals.
  #[local] Hint Resolve definition_upper_bound : wp_reals.
  #[local] Hint Resolve definition_lower_bound : wp_reals.
  #[local] Hint Resolve definition_bounded_above : wp_reals.
  #[local] Hint Resolve definition_bounded_below : wp_reals.

  #[local] Hint Resolve _sup_behaves_as_bound : wp_reals.
  #[local] Hint Resolve _inf_behaves_as_bound : wp_reals.

  (** The supremum introduced here equals the one from the 'completeness' axiom
    in the standard Coq library. *)
  Check definition_bounded_above.

  Lemma _bdd_above_implies_bound : A is bounded from above -> bound A.
  Proof.
    Assume that (A is bounded from above).
    It holds that (there exists M : R, M is an upper bound for A).
    It holds that (there exists M : R, for all a : R, A a -> a <= M).
    We conclude that (bound A).
  Qed.

  Lemma _sup_is_standard (H1A : A is non-empty) (H2A : A is bounded from above) : 
    sup A = proj1_sig(_, _, completeness A
              (_bdd_above_implies_bound H2A) (proj1(_, _, definition_non_empty A) H1A)).
  Proof.
    Define M := (proj1_sig(_, _, completeness A
                  (_bdd_above_implies_bound H2A) (proj1(_, _, definition_non_empty A) H1A))).
    Time By definition_supremum it suffices to show that 
      (is_upper_bound A M ∧ (for all L : ℝ, is_upper_bound A L ⇨ M ≤ L)).
    Define HypM := (proj2_sig(_, _, completeness A
                      (_bdd_above_implies_bound H2A) (proj1(_, _, definition_non_empty A) H1A))).
    By HypM we conclude that 
      (M is an upper bound for A ∧ (for all L : ℝ, L is an upper bound for A ⇨ M ≤ L)).
  Qed.

  (** Proof that the infimum is the 'opposite' of the supremum. *)
  Local Definition _min (A : R -> Prop) (b : R) := there exists a : R, (A a) ∧ b = -a.
  (* TODO: limit scope of '_min' to this module?*)
  Declare Scope _definition_inf_scope.
  Notation "-' A" := (_min A) (at level 10) : _definition_inf_scope.
  Open Scope _definition_inf_scope.

  Lemma _prop1_min :
    forall a : R, A a -> -'A (-a).
  Proof.
    Take a : R. Assume that (A a).
    We need to show that (there exists x : R, (A x) ∧ -a = -x).
    Choose (a). We conclude that (A a ∧ -a = -a).
  Qed.

  Lemma _prop2_min :
  forall a : R, -'A a -> A (-a).
  Proof.
    Take a : R. Assume that (-'A a).
    It holds that (there exists x : R, A x ∧ a = -x) (i).
    Obtain x according to (i), so for x : R it holds that (A x ∧ a = -x).
    It holds that (-a = x).
    We conclude that (A (-a)).
  Qed.

  Lemma _nonempty_implies_min_nonempty :
    A is non-empty -> -'A is non-empty.
  Proof.
    Assume that (A is non-empty). It holds that (there exists a : R, A a) (i).
    Obtain a according to (i), so for a : R it holds that (A a). 
    It suffices to show that (there exists b : R, -'A b).
    Choose b := (-a). 
    By _prop1_min we conclude that (-'A b).
  Qed.

  Lemma _bdd_below_implies_min_bdd_above :
    A is bounded from below -> -'A is bounded from above.
  Proof.
    Assume that (A is bounded from below).
    It holds that (there exists l : R, l is a lower bound for A) (i).
    Obtain l according to (i), so for l : R it holds that (l is a lower bound for A) (ii).
    It suffices to show that (there exists L : R, L is an upper bound for -'A).
    Choose L := (-l). It suffices to show that (forall x : R, -'A x -> x <= L).
    Take x : R. Assume that (-'A x).
    By _prop2_min it holds that (A (-x)).
    Check ii.
    (*Fail By (ii) it holds that (l <= -x).*)
    It holds that (l <= -x).
    We conclude that (& x <= -l = L).
  Qed.

  Lemma _inf_is_opposite_sup (H1A : A is non-empty) (H2A : A is bounded from below) : 
    inf A = - sup (-' A).
  Proof.
    By _nonempty_implies_min_nonempty it holds that (-'A is non-empty).
    By _bdd_below_implies_min_bdd_above it holds that (-'A is bounded from above).
    (* ... so sup -A is well-defined. *)
    By definition_infimum it suffices to show that
      (-sup(-'A) is a lower bound for A
       ∧ (for all l : ℝ, l is a lower bound for A -> l ≤ -sup(-'A))).
    We show both statements.
    - We need to show that (-sup(-'A) is a lower bound for A).
      It suffices to show that (for all a : R, A a -> -sup(-'A) <= a).
      Take a : R. Assume that (A a).
      By _prop1_min it holds that (-'A (-a)).
      By definition_supremum it holds that (-a <= sup (-'A)).
      We conclude that (-sup(-'A) <= a).
    - We need to show that  
        (for all l : R, l is a lower bound for A -> l <= -sup -'A).
      Take l : R. Assume that (l is a lower bound for A).
      It suffices to show that (sup (-'A) <= -l).
      We claim that (-l is an upper bound for -'A).
      { (* seen before in _bdd_below_implies_min_bdd_above *)
        It suffices to show that (forall x : R, -'A x -> x <= -l).
        Take x : R. Assume that (-'A x).
        By _prop2_min it holds that (A (-x)).
        It holds that (l <= -x).
        We conclude that (x <= -l). 
      }
      By definition_supremum we conclude that (sup (-'A) <= -l).
    Qed.
    
    Close Scope _definition_inf_scope.

End ConsistencyResults.



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
    Obtain l according to (lub_a_prf), so for l : R it holds that (is_lub (EUn a) l).
    Take ε : ℝ; such that (ε > 0).
    By exists_almost_maximizer_ε it holds that (∃ y : ℝ, (EUn a) y ∧ y > l - ε) (iv).
    Obtain y according to (iv), so for y : R it holds that 
      ((EUn a) y ∧ y > l - ε) (v).
    Because (v) both (EUn a y) (vi) and (y > l - ε) hold.
    Expand the definition of EUn in (vi).
    That is, write (vi) as (there exists n : ℕ , y = a n).
    Obtain n according to (vi), so for n : nat it holds that (y = a n).
    Choose k := n.
    We need to show that (l - ε < a n).
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
      (∃ k : ℕ, a (Nn + k)%nat > sequence_ub a (i) Nn - 1 / (INR m + 1)) (ii).
    Obtain k according to (ii), so for k : nat it holds that
      (a (Nn + k)%nat > sequence_ub a i Nn - 1 / (m + 1)).
    Choose l := (Nn+k)%nat.
    We show both statements.
    - We need to show that (l ≥ Nn)%nat.
      We conclude that (l ≥ Nn)%nat.
    - We need to show that ( a l > sequence_ub a (i) Nn - 1 / (m + 1) ).
      We conclude that ( a l > sequence_ub a (i) Nn - 1 / (m + 1) ).
Qed.

Close Scope R_scope.
