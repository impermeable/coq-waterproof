(** * Strong induction principles

Authors:
    - Jim Portegies

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

Require Import Lia.
Require Import Arith.
Require Import ClassicalChoice.

(** Create constant sequence
*)
Definition create_seq_from_vec_0 (A : Type) (a : A) :=
    fun (n : nat) => a.

(** Given a sequence << g : nat -> A >> and an element << a : A >>
  create a new sequence << g 0, g 1, ..., g (k-1), a, a, a, ...>>.
*)
Definition create_seq_from_vec (A : Type)
              (k : nat) (g : nat -> A) (a : A) (n : nat) :=
    if lt_dec n k (* if n < k *)
      then (g n)
      else a.

(** Step in between for strong induction. 
<<complete_induction_help A a Su n >> stores the sequence 
obtained after applying the induction step << n - 1>> times.
*)
Definition complete_induction_help (A : Type) (a : A) 
  (Su : (nat -> A) -> nat -> A): nat -> (nat -> A).
Proof.
  intro m.
  induction m as [|m prev_func].
  * exact (fun n : nat => a). 
  * exact (fun n : nat => if lt_dec n (S m) then (prev_func n) else 
      Su prev_func m).
Defined.

(** The result of complete induction.
*)
Definition complete_induction (A : Type) (a : A) 
  (Su : (nat -> A) -> nat -> A): (nat -> A).
Proof.
  exact (fun n : nat => (complete_induction_help A a Su) n n).
Defined.

Lemma complete_induction_help_compare_3 (A : Type) (a : A) 
(Su : (nat -> A) -> nat -> A): forall k : nat,
  complete_induction_help A a Su (S k)= 
  (fun n : nat => if lt_dec n (S k) then
  ((complete_induction_help A a Su k) n) else 
      Su (complete_induction_help A a Su k) k).
Proof.
  intro k.
  reflexivity.
Qed.

Lemma complete_induction_help_compare_4 (A : Type) (a : A) 
(Su : (nat -> A) -> nat -> A) (prev_func : nat -> A):
  forall k : nat,
  (fun n : nat => if lt_dec n (S k) then
  (prev_func n) else 
      Su prev_func k) (S k) = Su prev_func k.
Proof.
  intro k.
  change ((if lt_dec (S k) (S k) then prev_func (S k)
  else Su prev_func k) = Su prev_func k).
  destruct (lt_dec (S k) (S k)).
  * assert (con : False) by lia.
    destruct con.
  * reflexivity.
Qed.

Lemma complete_induction_help_compare_5 (A : Type) (a : A) 
(Su : (nat -> A) -> nat -> A)
  (prev_func : nat -> A): forall k : nat,
  (fun n : nat => if lt_dec n (S k) then
  (prev_func n) else 
      Su prev_func k) = 
      create_seq_from_vec A (S k) prev_func (Su prev_func k).
Proof.
  intro k.
  reflexivity.
Qed.

Lemma complete_induction_help_compare_6 (A : Type) (a : A) 
(Su : (nat -> A) -> nat -> A): forall k : nat,
  complete_induction_help A a Su (S k) = 
    create_seq_from_vec A (S k) 
      (complete_induction_help A a Su k)
      (Su (complete_induction_help A a Su k) k).
Proof.
  intro k.
  reflexivity.
Qed.

Definition complete_induction_prop_help (P : nat -> Prop) : 
  P O -> (forall k : nat, (forall l : nat, (l <= k) -> P(l)) ->
           forall l : nat, (l <= S k) -> P(l)
         ) ->
    forall k : nat, forall l : nat, (l <= k) -> P l.
intros H1 H2.
induction k as [| k IHk].
* intro l.
  intro l_le_0.
  assert (e: l = 0) by lia.
  rewrite e.
  exact H1.
* apply H2.
  exact IHk.  
Defined.

Definition from_small_to_large_ind (P : nat -> Prop) :
(forall k : nat, (forall l : nat, (l <= k) -> P(l)) ->
  P (S k) ) -> (forall k : nat, (forall l : nat, (l <= k) -> P(l))
  -> forall l : nat, 
(l <= S k) -> P(l) ).
Proof.
  intros H k H1 l H2.
  destruct (lt_eq_lt_dec l (S k)) as [H3 | H4].
  * destruct H3 as [H5 | H6].
    + assert (H7 : (l <=k) ) by lia.
      auto.
    + rewrite H6.
      apply H.
      assumption.
  * lia.
Defined.

Definition complete_induction_prop (P : nat -> Prop) : 
  P O -> (forall k : nat,
  (forall l : nat, (l <= k) -> P(l)) ->
  P(S k) ) -> forall k : nat, P k.
Proof.
intros H1 H2 k.
apply (complete_induction_prop_help P H1
  (from_small_to_large_ind P H2) k k); trivial.
Defined.

Lemma complete_induction_help_compare_1 (A : Type) (a : A) 
(Su : (nat -> A) -> nat -> A): forall k : nat,
      (complete_induction_help A a Su (S k) k =
      complete_induction_help A a Su (k) k).
Proof.
  intro k.
  simpl.
  destruct (lt_dec k (S k)).
  * reflexivity.
  * assert (H: False) by lia. 
    destruct H.
Defined.

Lemma complete_induction_help_compare_2 (A : Type) (a : A) 
  (Su : (nat -> A) -> nat -> A):
  forall k : nat, forall l : nat, (l <= k)%nat -> 
      (complete_induction_help A a Su (S k) l =
      complete_induction_help A a Su (l) l).
Proof.
  intros k l.
  induction k as [|k IHk].
  * intro l_le_0.
    assert (l_eq_0 : (l = 0)%nat) by lia.
    rewrite l_eq_0.
    simpl.
    reflexivity.
  * intro l_le_Sk.
    destruct (lt_dec l (S k)).
    + rewrite <- IHk.
      simpl.
      destruct (lt_dec l (S (S k))).
      - destruct (lt_dec l (S k)).
        reflexivity.
        reflexivity.
      - assert (H : False) by lia.
        destruct H.
      - lia.
    + assert (H1 : l = S k) by lia.
      rewrite H1.
      apply complete_induction_help_compare_1.
Qed.

Lemma complete_induction_help_compare (A : Type) (a : A) 
  (Su : (nat -> A) -> nat -> A):
  forall k : nat, forall l : nat,
    (l <= k) ->
      (complete_induction_help A a Su k l =
      complete_induction A a Su l).
Proof.
  unfold complete_induction.
  intros k l l_le_k.
  destruct (lt_eq_lt_dec l k) as [Z1 | Z2].
  * destruct Z1 as [Z3 | Z4].
    + set (m := (k - 1)%nat).
      assert (H : k = S m) by lia.
      rewrite H.
      apply complete_induction_help_compare_2; lia.
    + rewrite Z4.
      reflexivity.
  * assert (H : False) by lia.
    destruct H.
Defined.

Lemma specified_strong_induction_principle : forall A : Type,
  forall P : (nat -> A) -> nat -> Prop,
  (forall f g : nat -> A, forall k : nat,
    (forall l : nat, (l <= k)%nat -> f l = g l) -> P f k -> P g k) ->
  forall Su : (nat -> A) -> nat -> A,
  forall a : A, forall w : P (fun n : nat => a) 0%nat,
  (forall k : nat,
    (forall l : nat, (l <= k)%nat -> P ((complete_induction_help A a Su) l) l)
    -> P ((complete_induction_help A a Su) (S k)) (S k))
  -> forall k : nat, P (complete_induction A a Su) k.
Proof.
  intros A P H_ext Su a w H_ind k.
  apply (H_ext (complete_induction_help A a Su (k)) 
    (complete_induction A a Su)).
  * unfold complete_induction.
    apply complete_induction_help_compare.
  * induction k as [|k IHk] using complete_induction_prop.
    + exact w.
    + apply H_ind; exact IHk.
Qed.

Definition induction_statement_interface : 
  forall A : Type, forall (P : (nat -> A) -> nat -> Prop), 
  (forall f g : (nat -> A), forall l : nat, (forall k : nat, (k <= l) -> f k = g k ) -> P f l -> P g l) ->
  {n_0 | P (create_seq_from_vec_0 A n_0) 0} -> 
  (forall n : nat -> A, forall k : nat, 
  { n_k_plus_1 | (forall l : nat, (l <= k) -> P n l) -> P (create_seq_from_vec A (S k) n n_k_plus_1) (S k) })
  -> { h | forall k : nat, P h k}.
Proof.
intros A P H_ext n_0_w_proof Su_full.
set (Su := (fun (n : nat -> A) (k : nat) => @proj1_sig _ _ (Su_full n k))).
set (h := (complete_induction A (proj1_sig n_0_w_proof) Su)).
exists h.
destruct n_0_w_proof as [n_0 w_n_0].
apply specified_strong_induction_principle.
* assumption.
* exact w_n_0.
* simpl. 
  intros k H1.
  set (n_k_plus_1 := @proj1_sig _ _ (Su_full (complete_induction_help A n_0 Su k) k)).
  assert (H0 : n_k_plus_1 = Su (complete_induction_help A n_0 Su k) k) by trivial.
  destruct (Su_full (complete_induction_help A n_0 Su k) k) as
    [p_n_k_plus_1 w_Su_full].
  assert (H3 : n_k_plus_1 = p_n_k_plus_1) by trivial.
  rewrite <- H0.
  rewrite H3.
  unfold create_seq_from_vec in w_Su_full.
  apply w_Su_full.
  intros l l_le_k.
  apply (H_ext (complete_induction_help A n_0 Su l)).
  + intros q q_le_l.
    assert (q_le_k : q <= k) by lia.
    rewrite (complete_induction_help_compare A n_0 Su l q).
    - rewrite (complete_induction_help_compare A n_0 Su k q).
      ** reflexivity.
      ** assumption.
    - assumption.
  + apply H1; assumption.
Defined.

Definition uncurry (A : Type) (Su : prod (nat -> A) nat -> A) (n : nat -> A) (k : nat) : A.
Proof.
  exact (Su (pair n k)).
Defined.

Definition induction_statement_interface_weak : 
  forall A : Type, forall (P : (nat -> A) -> nat -> Prop), 
  (forall f g : (nat -> A), forall l : nat, (forall k : nat, (k <= l) -> f k = g k ) -> P f l -> P g l) ->
  (exists n_0 : A, P (create_seq_from_vec_0 A n_0) 0) -> 
  (forall n : nat -> A, forall k : nat, 
  ( exists n_k_plus_1 : A, (forall l : nat, (l <= k) -> P n l) -> P (create_seq_from_vec A (S k) n n_k_plus_1) (S k) ))
  -> exists h : nat -> A, forall k : nat, P h k.
Proof.
intros A P H_ext n_0_w_proof Su_full.
destruct n_0_w_proof as [n_0 w_n_0].
Print prod.
assert (H : exists Su : (prod (nat -> A) nat) -> A, forall nk : prod (nat ->A) nat,
(forall l : nat, (l <= snd nk) -> P (fst nk) l) ->
P (create_seq_from_vec A (S (snd nk)) (fst nk) (Su nk)) (S (snd nk))).
{
  set (R := fun (nk : prod (nat ->A) nat) (a : A) => 
  (forall l : nat, (l <= snd nk) -> P (fst nk) l) ->
  P (create_seq_from_vec A (S (snd nk)) (fst nk) a) (S (snd nk))
  ).
  apply (@choice (prod (nat->A) nat) A R).
  intro nk.
  destruct nk as [n k].
  apply Su_full.
}

assert (H1 : exists Su : (nat->A) -> nat -> A, forall (n : (nat ->A)) (k : nat),
(forall l : nat, (l <= k) -> P n l) ->
P (create_seq_from_vec A (S k) n (Su n k)) (S (k))).
{
  destruct H as [SuCurried w_Su_curried].
  exists (fun n k => SuCurried (pair n k)).
  intros n k H2.
  apply (w_Su_curried (pair n k)).
  apply H2.
}
destruct H1 as [Su w_Su].
set (h := (complete_induction A n_0 Su)).
exists h.
apply specified_strong_induction_principle.
* assumption.
* exact w_n_0.
* simpl. 
  intros k H1.
  set (n_k_plus_1 := Su (complete_induction_help A n_0 Su k) k).
  apply w_Su.
  intros l l_le_k.
  apply (H_ext (complete_induction_help A n_0 Su l)).
  + intros q q_le_l.
    assert (q_le_k : q <= k) by lia.
    rewrite (complete_induction_help_compare A n_0 Su l q).
    - rewrite (complete_induction_help_compare A n_0 Su k q).
      ** reflexivity.
      ** assumption.
    - assumption.
  + apply H1; assumption.
Defined.

(** Construct subsequences with certain properties. *)

(** Add subsequence property.
*)
Definition add_subsequence_property (myQ: nat->nat->Prop)
  (n : nat -> nat) k : Prop :=
  match k with 
  | O => myQ (n O) O
  | S m => ((n k) > n (Nat.pred k))%nat /\ (myQ (n k) k)
  end.

Lemma propositions_with_subsequence_property_satisfy_no_lookahead : forall (myQ: nat->nat->Prop),
forall (f g : nat -> nat) (l : nat),
(forall k : nat,
   (k <= l) -> f (k) = g (k)) -> add_subsequence_property myQ f l -> add_subsequence_property myQ g l.
Proof.
  intros myQ f g l H.
  unfold add_subsequence_property.
  intro myPf.
  destruct l as [|l].
  * rewrite <- H.
    apply myPf.
    trivial.
  * rewrite <- H.
    rewrite <- (H (Nat.pred (S l))).
    apply myPf.
    + lia.
    + lia.
Qed.

Definition induction_principle_subsequence_with_prop : 
  forall (myQ : nat->nat->Prop), 
  { n_0 | myQ n_0 O } -> 
  (forall n : nat -> nat, forall k : nat, 
  { n_k_plus_1 | (forall l : nat, (l <= k) -> add_subsequence_property myQ n l)
    -> add_subsequence_property myQ (create_seq_from_vec nat (S k) n n_k_plus_1) (S k) })
  -> { h | forall k : nat, add_subsequence_property myQ h k}.
Proof.
  intros myQ n_0_w_proof H_ind.
  apply induction_statement_interface.
  * apply propositions_with_subsequence_property_satisfy_no_lookahead.
  * destruct n_0_w_proof as [n_0 w_n_0].
    exists n_0.
    unfold create_seq_from_vec_0.
    exact w_n_0.
  * exact H_ind.
Defined.

Definition induction_principle_subsequence_with_prop_weak : 
  forall (myQ : nat->nat->Prop), 
  ( exists n_0, myQ n_0 O ) -> 
  (forall n : nat -> nat, forall k : nat, 
  ( exists n_k_plus_1, (forall l : nat, (l <= k) -> add_subsequence_property myQ n l)
    -> add_subsequence_property myQ (create_seq_from_vec nat (S k) n n_k_plus_1) (S k) ))
  -> exists h, forall k : nat, add_subsequence_property myQ h k.
Proof.
  intros myQ n_0_w_proof H_ind.
  apply induction_statement_interface_weak.
  * apply propositions_with_subsequence_property_satisfy_no_lookahead.
  * destruct n_0_w_proof as [n_0 w_n_0].
    exists n_0.
    unfold create_seq_from_vec_0.
    exact w_n_0.
  * exact H_ind.
Defined.

(** Example

*)

Section SubsequenceExample.

Local Parameter Q : nat -> nat -> Prop.
Local Parameter exists_larger_element : forall m : nat, forall k : nat, { l : nat | l >= k /\ Q l m}.

Lemma exists_subsequence_example:
  { n : nat -> nat | 
    forall k : nat, add_subsequence_property Q n k }.
Proof.
  apply induction_principle_subsequence_with_prop.
  * destruct (exists_larger_element 0 0) as [l w_l].
    exists l.
    exact (proj2 w_l).
  * intros n k.
    destruct (exists_larger_element (S k) (n k + 1)) as [l w_l].
    exists l.
    unfold create_seq_from_vec.
    intro H.
    unfold add_subsequence_property.
    destruct (lt_dec (S k) (S k)).
    + assert (con : False) by lia.
      destruct con.
    + destruct (lt_dec (Nat.pred (S k)) (S k)).
      - split.
        change (l > n k).
        destruct w_l.
        lia.
        destruct w_l.
        exact H1.
      - destruct w_l.
        assert (con : False) by lia.
        destruct con.
Defined.  

Local Parameter exists_larger_element_weak : forall m : nat, forall k : nat, exists l : nat, l >= k /\ Q l m.

Lemma exists_subsequence_example_weak:
  exists n : nat -> nat,
    forall k : nat, add_subsequence_property Q n k.
Proof.
  apply induction_principle_subsequence_with_prop_weak.
  * destruct (exists_larger_element 0 0) as [l w_l].
    exists l.
    exact (proj2 w_l).
  * intros n k.
    destruct (exists_larger_element (S k) (n k + 1)) as [l w_l].
    exists l.
    unfold create_seq_from_vec.
    intro H.
    unfold add_subsequence_property.
    destruct (lt_dec (S k) (S k)).
    + assert (con : False) by lia.
      destruct con.
    + destruct (lt_dec (Nat.pred (S k)) (S k)).
      - split.
        change (l > n k).
        destruct w_l.
        lia.
        destruct w_l.
        exact H1.
      - destruct w_l.
        assert (con : False) by lia.
        destruct con.
Defined. 

End SubsequenceExample.