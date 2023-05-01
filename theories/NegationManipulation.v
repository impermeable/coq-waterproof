Require Import Classical_Prop.
Require Import Classical_Pred_Type.

Lemma or_func (A B C D : Prop) :
  (A -> C) -> (B -> D) -> (A \/ B) -> (C \/ D).
Proof. 
  intros a_to_c b_to_d ab. 
  destruct ab as [a | b].
  left; exact (a_to_c a). 
  right; exact (b_to_d b). 
Qed.

Lemma and_func (A B C D : Prop) :
  (A -> C) -> (B -> D) -> (A /\ B) -> (C /\ D).
Proof. 
  intros a_to_c b_to_d ab. 
  destruct ab as [a b]. 
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
  tauto.
Qed.

(* Reverse *)
Lemma and_not_or_func (A B C D : Prop) :
  (C -> ~A) -> (D -> ~B) -> (C /\ D) -> ~(A \/ B).
Proof. 
  intros c_to_na d_to_nb cd.
  tauto.
Qed.

Lemma not_and_or_func (A B C D : Prop) :
  (~A -> C) -> (~B -> D) -> ~(A /\ B) -> (C \/ D).
Proof. 
  intros na_to_c nb_to_d nab.
  tauto.
Qed.

(* Reverse *)
Lemma or_not_and_func (A B C D : Prop) :
  (C -> ~A) -> (D -> ~B) -> (C \/ D) -> ~(A /\ B).
Proof. 
  intros c_to_na d_to_nb cd.
  tauto.
Qed.

Lemma not_and_impl_func (A B C : Prop) :
  (~B -> C) -> ~(A /\ B) -> (A -> C).
Proof. 
  intros nb_to_c nab.
  tauto.
Qed.

(* Reverse *)
Lemma impl_not_and_func (A B C : Prop) :
  (C -> ~B) -> (A -> C) -> ~(A /\ B).
Proof. 
  intros c_to_nb a_to_c.
  tauto.
Qed.

Lemma not_impl_and_func (A B C : Prop) :
  (~B -> C) -> ~(A -> B) -> (A /\ C).
Proof.
  intros nb_to_c not_a_to_b.
  tauto.
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
  apply not_all_ex_not in notallx_Px.
  destruct notallx_Px.
  exists x.
  apply allx_notPx_to_Qx.
  assumption.
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
  intuition.
  apply allx_notPx_to_Qx.
  intros Px.
  apply notsomex_Px.
  exists x.
  assumption.
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