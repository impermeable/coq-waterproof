(** * [propagate_negation_backwards.v]
Authors: 
    - Jelle Wemmenhove
Creation date: 2 Nov 2021

TODO: description

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
From Ltac2 Require Import Message.



Require Import Waterproof.auxiliary.
Require Import Classical_Prop.
Require Import Classical_Pred_Type.

Ltac2 Type exn ::= [ NegationError(string) ].




Lemma or_func (A B C D : Prop) :
  (A -> C) -> (B -> D) -> (A \/ B) -> (C \/ D).
Proof. intros a_to_c b_to_d ab. destruct ab as [a | b].
       left; exact (a_to_c a). right; exact (b_to_d b). Qed.
Lemma and_func (A B C D : Prop) :
  (A -> C) -> (B -> D) -> (A /\ B) -> (C /\ D).
Proof. intros a_to_c b_to_d ab. destruct ab as [a b]. 
       exact (conj (a_to_c a) (b_to_d b)). Qed.
Lemma impl_func (A B C D : Prop) :
  (C -> A) -> (B -> D) -> (A -> B) -> (C -> D).
Proof. intros c_to_a b_to_d a_to_b c. exact (b_to_d (a_to_b (c_to_a c))). Qed.

Lemma all_func (A : Type) (P Q : A -> Prop) : 
  (forall x, P x -> Q x) -> (forall x, P x) -> (forall x, Q x).
Proof. intros allx_Px_to_Qx allx_Px x. exact ((allx_Px_to_Qx x) (allx_Px x)). Qed.
Lemma ex_func (A : Type) (P Q : A -> Prop) : 
  (forall x, P x -> Q x) -> (exists x, P x) -> (exists x, Q x).
Proof. intros allx_Px_to_Qx somex_Px. destruct somex_Px as [x Px]. exists x. exact (allx_Px_to_Qx x Px). Qed.



Lemma not_or_and_func (A B C D : Prop) :
  (~A -> C) -> (~B -> D) -> ~(A \/ B) -> (C /\ D).
Proof. 
  intros na_to_c nb_to_d nab.
  ltac1:(cut (~A /\ ~B)).
  apply (and_func). exact na_to_c. exact nb_to_d.
  apply not_or_and. exact nab.
Qed.
(* reverse *)
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
  apply (or_func). exact na_to_c. exact nb_to_d.
  apply not_and_or. exact nab.
Qed.
(* reverse *)
Lemma or_not_and_func (A B C D : Prop) :
  (C -> ~A) -> (D -> ~B) -> (C \/ D) -> ~(A /\ B).
Proof. 
  intros c_to_na d_to_nb cd.
  ltac1:(cut (~A \/ ~B)).
  apply (or_not_and).
  destruct cd as [c | d].
  left; exact (c_to_na c). right; exact (d_to_nb d).
Qed.

Lemma not_impl_and_func (A B C : Prop) :
  (~B -> C) -> ~(A -> B) -> (A /\ C).
Proof.
  intros nb_to_c not_a_to_b.
  ltac1:(cut (A /\ ~B)).
  apply and_func. exact id. exact nb_to_c.
  apply imply_to_and. exact not_a_to_b.
Qed.
(* reverse *)
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
  apply ex_func. exact allx_notPx_to_Qx.
  apply not_all_ex_not. exact notallx_Px.
Qed.
(* reverse *)
Lemma ex_not_all_func (A : Type) (P Q : A -> Prop) : 
  (forall x, Q x -> ~P x) -> (exists x, Q x) -> (~forall x, P x).
Proof. 
  intros allx_Qx_to_notPx somex_Qx.
  apply ex_not_not_all.
  destruct somex_Qx as [x Qx].
  exists x. exact ((allx_Qx_to_notPx x) Qx).
Qed.

Lemma not_ex_all_func (A : Type) (P Q : A -> Prop) : 
  (forall x, ~P x -> Q x) -> (~exists x, P x) -> (forall x, Q x).
Proof. 
  intros allx_notPx_to_Qx notsomex_Px.
  ltac1:(cut (forall x, ~P x)).
  apply all_func. exact allx_notPx_to_Qx.
  apply not_ex_all_not. exact notsomex_Px.
Qed.

Lemma all_not_ex_func (A : Type) (P Q : A -> Prop) : 
  (forall x, Q x -> ~P x) -> (forall x, Q x) -> (~exists x, P x).
Proof. 
  intros allx_Qx_to_notPx allx_Qx.
  apply all_not_not_ex.
  intro x. exact ((allx_Qx_to_notPx x) (allx_Qx x)).
Qed.

Lemma not_neg_pos_func (A B : Prop) : 
  (A -> B) -> (~~A -> B).
Proof. intros a_to_b nna. exact (a_to_b (NNPP A nna)). Qed.
(* reverse *)
Lemma pos_not_neg_func (A B : Prop) : 
  (B -> A) -> (B -> ~~A).
Proof. intros b_to_a b na. exact (na (b_to_a b)). Qed.



(** Tactic *)
Local Ltac2 solve_by_manipulating_negation_in (h_id : ident) :=
  let h := Control.hyp h_id in
  (* Check whether h is a proposition. *)
  let type_h := Aux.get_value_of_hyp h in
  let sort_h := Aux.get_value_of_hyp type_h in
  match Aux.check_constr_equal sort_h constr:(Prop) with
  | false => Control.zero (NegationError
                         "Can only manipulate negation in propositions.")
  | true => 
      let attempt () :=
        revert $h_id;
        solve[ repeat (first [ (* finish proof *)
                               exact (fun x => x) 
                             | (* without negation *)
                               apply or_func
                             | apply and_func
                             | apply impl_func
                             | apply all_func; let x_id := Fresh.in_goal @x in intro $x_id
                             | apply ex_func; let x_id := Fresh.in_goal @x in intro $x_id
                             | (* with negation *)
                               apply not_or_and_func
                             | apply and_not_or_func
                             | apply not_and_or_func
                             | apply or_not_and_func
                             | apply not_impl_and_func
                             | apply and_not_impl_func
                             | apply not_all_ex_func; let x_id := Fresh.in_goal @x in intro $x_id
                             | apply ex_not_all_func; let x_id := Fresh.in_goal @x in intro $x_id
                             | apply not_ex_all_func; let x_id := Fresh.in_goal @x in intro $x_id
                             | apply all_not_ex_func; let x_id := Fresh.in_goal @x in intro $x_id
                             | apply not_neg_pos_func
                             | apply pos_not_neg_func
                             ])]
      in
      match Control.case attempt with
      | Val _ => ()
      | Err exn => Control.zero (NegationError "Failed to solve by manipulating negation.")
      end
  end.


Local Ltac2 solve_by_manipulating_negation () :=
  match! goal with
  | [ h : _ |- _ ] => solve_by_manipulating_negation_in h
  end.
