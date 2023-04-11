(** * [manipulate_negation.v]
Authors: 
    - Jelle Wemmenhove
Creation date: 2 Nov 2021

Try to prove the current goal from a hypothesis by manipulating negations, 
meaning that we interchange negations and logical operators. For example, this tactic 
can show that (¬∀x∃y∀z,P(x,y,z) implies ∃x∀y∃z, ¬P(x,y,z)).

Context specific manipulations can added by including them in the 
[global_negation_database_selection].

This tactic ([solve_by_manipulating_negation]) is added to the [classical_logic]
hint database.

--------------------------------------------------------------------------------

This file is part of Waterproof-lib.

Waterproof-lib is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

Waterproof-lib is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with Waterproof-lib.  If not, see <https://www.gnu.org/licenses/>.
*)

From Ltac2 Require Import Ltac2.
From Ltac2 Require Option.


Require Import Waterproof.message.

Require Import Waterproof.auxiliary.
Require Import Waterproof.init_automation_global_variables.
Require Import Waterproof.waterprove.automation_subroutine.

Require Import Classical_Prop.
Require Import Classical_Pred_Type.

Ltac2 Type exn ::= [ NegationError(string) ].

Lemma or_func (A B C D : Prop) :
  (A -> C) -> (B -> D) -> (A \/ B) -> (C \/ D).
Proof. intros a_to_c b_to_d ab. destruct ab as [a | b].
  left; exact (a_to_c a). 
  right; exact (b_to_d b). 
Qed.

Lemma and_func (A B C D : Prop) :
  (A -> C) -> (B -> D) -> (A /\ B) -> (C /\ D).
Proof. intros a_to_c b_to_d ab. destruct ab as [a b]. 
  exact (conj (a_to_c a) (b_to_d b)).
Qed.

Lemma impl_func (A B C D : Prop) :
  (C -> A) -> (B -> D) -> (A -> B) -> (C -> D).
Proof. 
  intros c_to_a b_to_d a_to_b c.
  exact (b_to_d (a_to_b (c_to_a c))).
Qed.

Lemma all_func (A : Type) (P Q : A -> Prop) : 
  (forall x, P x -> Q x) -> (forall x, P x) -> (forall x, Q x).
Proof. 
  intros allx_Px_to_Qx allx_Px x.
  exact ((allx_Px_to_Qx x) (allx_Px x)).
Qed.

Lemma ex_func (A : Type) (P Q : A -> Prop) : 
  (forall x, P x -> Q x) -> (exists x, P x) -> (exists x, Q x).
Proof.
  intros allx_Px_to_Qx somex_Px.
  destruct somex_Px as [x Px].
  exists x.
  exact (allx_Px_to_Qx x Px).
Qed.


Lemma not_or_and_func (A B C D : Prop) :
  (~A -> C) -> (~B -> D) -> ~(A \/ B) -> (C /\ D).
Proof. 
  intros na_to_c nb_to_d nab.
  ltac1:(cut (~A /\ ~B)).
  apply (and_func).
  exact na_to_c.
  exact nb_to_d.
  apply not_or_and.
  exact nab.
Qed.

(* Reverse *)
Lemma and_not_or_func (A B C D : Prop) :
  (C -> ~A) -> (D -> ~B) -> (C /\ D) -> ~(A \/ B).
Proof. 
  intros c_to_na d_to_nb cd.
  ltac1:(cut (~A /\ ~B)).
  apply (and_not_or). 
  exact (conj (c_to_na (proj1 cd)) (d_to_nb (proj2 cd))).
Qed.

Lemma not_and_or_func (A B C D : Prop) :
  (~A -> C) -> (~B -> D) -> ~(A /\ B) -> (C \/ D).
Proof. 
  intros na_to_c nb_to_d nab.
  ltac1:(cut (~A \/ ~B)).
  apply (or_func).
  exact na_to_c.
  exact nb_to_d.
  apply not_and_or.
  exact nab.
Qed.

(* Reverse *)
Lemma or_not_and_func (A B C D : Prop) :
  (C -> ~A) -> (D -> ~B) -> (C \/ D) -> ~(A /\ B).
Proof. 
  intros c_to_na d_to_nb cd.
  ltac1:(cut (~A \/ ~B)).
  apply (or_not_and).
  destruct cd as [c | d].
  left; exact (c_to_na c).
  right; exact (d_to_nb d).
Qed.

Lemma not_and_impl_func (A B C : Prop) :
  (~B -> C) -> ~(A /\ B) -> (A -> C).
Proof. 
  intros nb_to_c nab.
  ltac1:(cut (~A \/ C)).
  apply or_to_imply.
  ltac1:(cut (~A \/ ~B)).
  apply or_func.
  exact id.
  exact nb_to_c.
  apply not_and_or.
  exact nab.
Qed.

(* Reverse *)
Lemma impl_not_and_func (A B C : Prop) :
  (C -> ~B) -> (A -> C) -> ~(A /\ B).
Proof. 
  intros c_to_nb a_to_c.
  ltac1:(cut (~A \/ ~B)).
  apply (or_not_and).
  ltac1:(cut (~A \/ C)).
  apply or_func.
  exact id.
  exact c_to_nb.
  apply imply_to_or.
  exact a_to_c.
Qed.

Lemma not_impl_and_func (A B C : Prop) :
  (~B -> C) -> ~(A -> B) -> (A /\ C).
Proof.
  intros nb_to_c not_a_to_b.
  ltac1:(cut (A /\ ~B)).
  apply and_func.
  exact id.
  exact nb_to_c.
  apply imply_to_and.
  exact not_a_to_b.
Qed.

(* Reverse *)
Lemma and_not_impl_func (A B C : Prop) :
  (C -> ~B) -> (A /\ C) -> ~(A -> B).
Proof.
  intros c_to_nb ac a_to_b.
  exact ((c_to_nb (proj2 ac)) (a_to_b (proj1 ac))).
Qed.

Lemma not_all_ex_func (A : Type) (P Q : A -> Prop) : 
  (forall x, ~P x -> Q x) -> (~forall x, P x) -> (exists x, Q x).
Proof. 
  intros allx_notPx_to_Qx notallx_Px.
  ltac1:(cut (exists x, ~P x)).
  apply ex_func.
  exact allx_notPx_to_Qx.
  apply not_all_ex_not.
  exact notallx_Px.
Qed.

(* Reverse *)
Lemma ex_not_all_func (A : Type) (P Q : A -> Prop) : 
  (forall x, Q x -> ~P x) -> (exists x, Q x) -> (~forall x, P x).
Proof. 
  intros allx_Qx_to_notPx somex_Qx.
  apply ex_not_not_all.
  destruct somex_Qx as [x Qx].
  exists x.
  exact ((allx_Qx_to_notPx x) Qx).
Qed.

Lemma not_ex_all_func (A : Type) (P Q : A -> Prop) : 
  (forall x, ~P x -> Q x) -> (~exists x, P x) -> (forall x, Q x).
Proof. 
  intros allx_notPx_to_Qx notsomex_Px.
  ltac1:(cut (forall x, ~P x)).
  apply all_func.
  exact allx_notPx_to_Qx.
  apply not_ex_all_not.
  exact notsomex_Px.
Qed.

Lemma all_not_ex_func (A : Type) (P Q : A -> Prop) : 
  (forall x, Q x -> ~P x) -> (forall x, Q x) -> (~exists x, P x).
Proof. 
  intros allx_Qx_to_notPx allx_Qx.
  apply all_not_not_ex.
  intro x.
  exact ((allx_Qx_to_notPx x) (allx_Qx x)).
Qed.

Lemma not_neg_pos_func (A B : Prop) : 
  (A -> B) -> (~~A -> B).
Proof. intros a_to_b nna. exact (a_to_b (NNPP A nna)). Qed.

(* Reverse *)
Lemma pos_not_neg_func (A B : Prop) : 
  (B -> A) -> (B -> ~~A).
Proof.
  intros b_to_a b na.
  exact (na (b_to_a b)).
Qed.

(** Tactic *)
Local Ltac2 solve_by_manipulating_negation_in (h_id : ident) :=
  let h := Control.hyp h_id in
  
  (* Check whether h is a proposition. *)
  let type_h := Aux.get_value_of_hyp h in
  let sort_h := Aux.get_value_of_hyp type_h in
  match Aux.check_constr_equal sort_h constr:(Prop) with
  | false => Control.zero (NegationError "Can only manipulate negation in propositions.")
  | true => 
    let attempt () :=
      revert $h_id;
      solve[ 
        repeat (
          first [ (* finish proof *)
            exact id 
            (* without negation *)
            | lazy_match! goal with
              | [ |- (?a \/ ?b) -> (?c \/ ?d)] => apply (or_func $a $b $c $d)
              | [ |- (?a /\ ?b) -> (?c /\ ?d)] => apply (and_func $a $b $c $d)
              | [ |- (?a -> ?b) -> (?c -> ?d)] => apply (impl_func $a $b $c $d)
              (* matching on a forall statement !!! *)
              | [ |- (forall x, @?p x) -> (forall x, @?q x)] => apply (all_func _ $p $q); let x_id := Fresh.in_goal @x in intro $x_id
              | [ |- (exists x, @?p x) -> (exists x, @?q x)] => apply (ex_func _ $p $q); let x_id := Fresh.in_goal @x in intro $x_id

              (* with negation *)
              | [ |- ~(?a \/ ?b) -> (?c /\ ?d)] => apply (not_or_and_func $a $b $c $d)
              | [ |- (?c /\ ?d) -> ~(?a \/ ?b)] => apply (not_or_and_func $a $b $c $d)
              | [ |- ~(?a /\ ?b) -> (?c \/ ?d)] => apply (not_and_or_func $a $b $c $d)
              | [ |- (?c \/ ?d) -> ~(?a /\ ?b)] => apply (or_not_and_func $a $b $c $d)
              | [ |- ~(?a /\ ?b) -> (?a -> ?c)] => apply (not_and_impl_func $a $b $c)
              | [ |- (?a -> ?c) -> ~(?a /\ ?b)] => apply (impl_not_and_func $a $b $c)
              | [ |- ~(?a -> ?b) -> (?a /\ ?c)] => apply (not_impl_and_func $a $b $c)
              | [ |- (?a /\ ?c) -> ~(?a -> ?b)] => apply (and_not_impl_func $a $b $c)
              | [ |- ~(forall x, @?p x) -> (exists x, @?q x)] => apply (not_all_ex_func _ $p $q); let x_id := Fresh.in_goal @x in intro $x_id
              | [ |- (exists x, @?q x) -> ~(forall x, @?p x)] => apply (ex_not_all_func _ $p $q); let x_id := Fresh.in_goal @x in intro $x_id
              | [ |- ~(exists x, @?p x) -> (forall x, @?q x)] => apply (not_ex_all_func _ $p $q); let x_id := Fresh.in_goal @x in intro $x_id
              | [ |- (forall x, @?q x) -> ~(exists x, @?p x)] => apply (all_not_ex_func _ $p $q); let x_id := Fresh.in_goal @x in intro $x_id
              | [ |- (~~?a) -> ?b] => apply (not_neg_pos_func $a $b)
              | [ |- ?b -> (~~?a)] => apply (pos_not_neg_func $a $b)
            end
            | (* Try context specific manipulation, e.g. negating order relations *)
              let g := Control.goal () in
              let hint_databases := Some (global_negation_database_selection ()) in
              run_automation g [] 1 hint_databases false
          ] 
        ) 
      ]
      in
      match Control.case attempt with
        | Val _ => ()
        | Err exn => Control.zero (NegationError "Failed to solve by manipulating negation.")
      end
  end.


Ltac2 solve_by_manipulating_negation () :=
  match! goal with
    | [ h : _ |- _ ] => solve_by_manipulating_negation_in h
  end.

(*For debugging: do a single step *)
Local Ltac2 manipulate_negation_in (h_id : ident) :=
  let h := Control.hyp h_id in
  (* Check whether h is a proposition. *)
  let type_h := Aux.get_value_of_hyp h in
  let sort_h := Aux.get_value_of_hyp type_h in
  match Aux.check_constr_equal sort_h constr:(Prop) with
  | false => Control.zero (NegationError "Can only manipulate negation in propositions.")
  | true => 
    let attempt () :=
      revert $h_id; 
      print (of_constr (Control.goal ()));
      first [ (* finish proof *)
        exact id
        | lazy_match! goal with
                (* without negation *)
          | [ |- (?a \/ ?b) -> (?c \/ ?d)] => apply (or_func $a $b $c $d)
          | [ |- (?a /\ ?b) -> (?c /\ ?d)] => apply (and_func $a $b $c $d)
          | [ |- (?a -> ?b) -> (?c -> ?d)] => apply (impl_func $a $b $c $d)
          | [ |- (forall x, @?p x) -> (forall x, @?q x)] => apply (all_func _ $p $q); let x_id := Fresh.in_goal @x in intro $x_id
          | [ |- (exists x, @?p x) -> (exists x, @?q x)] => apply (ex_func _ $p $q); let x_id := Fresh.in_goal @x in intro $x_id

          (* with negation *)
          | [ |- ~(?a \/ ?b) -> (?c /\ ?d)] => apply (not_or_and_func $a $b $c $d)
          | [ |- (?c /\ ?d) -> ~(?a \/ ?b)] => apply (and_not_or_func $a $b $c $d)
          | [ |- ~(?a /\ ?b) -> (?c \/ ?d)] => apply (not_and_or_func $a $b $c $d)
          | [ |- (?c \/ ?d) -> ~(?a /\ ?b)] => apply (or_not_and_func $a $b $c $d)
          | [ |- ~(?a /\ ?b) -> (?a -> ?c)] => apply (not_and_impl_func $a $b $c)
          | [ |- (?a -> ?c) -> ~(?a /\ ?b)] => apply (impl_not_and_func $a $b $c)
          | [ |- ~(?a -> ?b) -> (?a /\ ?c)] => apply (not_impl_and_func $a $b $c)
          | [ |- (?a /\ ?c) -> ~(?a -> ?b)] => apply (and_not_impl_func $a $b $c)
          | [ |- ~(forall x, @?p x) -> (exists x, @?q x)] => apply (not_all_ex_func _ $p $q); let x_id := Fresh.in_goal @x in intro $x_id
          | [ |- (exists x, @?q x) -> ~(forall x, @?p x)] => apply (ex_not_all_func _ $p $q); let x_id := Fresh.in_goal @x in intro $x_id
          | [ |- ~(exists x, @?p x) -> (forall x, @?q x)] => apply (not_ex_all_func _ $p $q); let x_id := Fresh.in_goal @x in intro $x_id
          | [ |- (forall x, @?q x) -> ~(exists x, @?p x)] => apply (all_not_ex_func _ $p $q); let x_id := Fresh.in_goal @x in intro $x_id
          | [ |- (~~?a) -> ?b] => apply (not_neg_pos_func $a $b)
          | [ |- ?b -> (~~?a)] => apply (pos_not_neg_func $a $b)
          end
        | (* Try context specific manipulation, e.g. negating order relations *)
          let g := Control.goal () in
          let hint_databases := Some (global_negation_database_selection ()) in
          run_automation g [] global_search_depth hint_databases false
      ]
      in
      match Control.case attempt with
        | Val _ => ()
        | Err exn => Control.zero (exn)
      end
  end.
