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
Require Import ClassicalChoice.
Require Import Lia.

Require Import Automation.
Require Import Libs.Negation.
Require Import Notations.
Require Import Tactics.

Waterproof Enable Automation RealsAndIntegers.

Definition create_seq_from_vec_0 (A : Type) (a : A) :=
    fun (n : nat) => a.

Definition create_seq_from_vec (A : Type)
              (k : ℕ) (g : ℕ → A) (a : A) (n : ℕ) :=
    if lt_dec n (k)%nat (* if n < k *)
      then (g n)
      else a.

Local Parameter Q : nat -> Prop.
Definition Z := fun (n : nat) => True.

Definition complete_induction_help (A : Type) (a : A) 
  (Su : (ℕ → A) → ℕ → A): ℕ → (ℕ → A).
Proof.
  intro m.
  induction m as [|m prev_func].
  * exact (fun n : ℕ => a). 
  * exact (fun n : ℕ => if lt_dec n (S m) then (prev_func n) else 
      Su prev_func m).
Defined.

Lemma le0_impl_0 : forall k : nat, (k <= 0)%nat -> k = O.
Proof.
  intro k.
  auto with zarith.
Defined.

Definition complete_induction (A : Type) (a : A) 
(Su : (ℕ → A) → ℕ → A): (ℕ → A).
Proof.
  exact (fun n : ℕ => (complete_induction_help A a Su) n n).
Defined.

Lemma complete_induction_help_compare_3 (A : Type) (a : A) 
(Su : (ℕ → A) → ℕ → A): forall k : nat,
  complete_induction_help A a Su (S k)= 
  (fun n : ℕ => if lt_dec n (S k) then
  ((complete_induction_help A a Su k) n) else 
      Su (complete_induction_help A a Su k) k).
Proof.
  intro k.
  reflexivity.
Qed.

Lemma complete_induction_help_compare_4 (A : Type) (a : A) 
(Su : (ℕ → A) → ℕ → A) (prev_func : nat -> A): forall k : nat,
  (fun n : ℕ => if lt_dec n (S k) then
  (prev_func n) else 
      Su prev_func k) (S k) = Su prev_func k.
Proof.
  intro k.
  change ((if lt_dec (S k) (S k) then prev_func (S k)
  else Su prev_func k) = Su prev_func k).
  destruct (lt_dec (S k) (S k)).
  assert (con : False) by auto with zarith.
  destruct con.
  reflexivity.
Qed.

Lemma complete_induction_help_compare_5 (A : Type) (a : A) 
(Su : (ℕ → A) → ℕ → A) (prev_func : nat -> A): forall k : nat,
  (fun n : ℕ => if lt_dec n (S k) then
  (prev_func n) else 
      Su prev_func k) = 
      create_seq_from_vec A (S k) prev_func (Su prev_func k).
Proof.
  intro k.
  unfold create_seq_from_vec.
  reflexivity.
Qed.

Lemma complete_induction_help_compare_6 (A : Type) (a : A) 
(Su : (ℕ → A) → ℕ → A): forall k : nat,
  complete_induction_help A a Su (S k) = 
    create_seq_from_vec A (S k) 
      (complete_induction_help A a Su k)
      (Su (complete_induction_help A a Su k) k).
Proof.
  intro k.
  unfold create_seq_from_vec.
  reflexivity.
Qed.

Definition complete_induction_prop_help (P : nat -> Prop) : 
  P O -> (forall k : nat, (forall l : nat, (l <= k)%nat -> P(l)) -> forall l : nat, 
    (l <= S k)%nat -> P(l) ) -> forall k : nat, forall l : nat, (l <= k)%nat -> P l.
intros H1 H2.
induction k as [| k IHk].
* intro l.
  intro l_le_0.
  pose (e := le0_impl_0 l l_le_0).
  rewrite e.
  exact H1.
* apply H2.
  apply IHk.  
Defined.

Definition from_small_to_large_ind (P : nat -> Prop) :
(forall k : nat, (forall l : nat, (l <= k)%nat -> P(l)) ->
  P (S k) ) -> (forall k : nat, (forall l : nat, (l <= k)%nat -> P(l)) -> forall l : nat, 
(l <= S k)%nat -> P(l) ).
Proof.
  intro H.
  intro k.
  intro H1.
  intro l.
  intro H2.
  destruct (lt_eq_lt_dec l (S k)) as [H3 | H4].
  destruct H3 as [H5 | H6].
  assert (H7 : (l <=k)%nat ) by (auto with zarith).
  auto.
  rewrite H6.
  apply H.
  assumption.
  auto with zarith.
Defined.

Definition complete_induction_prop (P : nat -> Prop) : 
  P O -> (forall k : nat,
  (forall l : nat, (l <= k)%nat -> P(l)) ->
  P(S k) ) -> forall k : nat, P k.
Proof.
intros H1 H2.
intro k.
apply (complete_induction_prop_help P H1 (from_small_to_large_ind P H2)
  k k).
  trivial.
Defined.
Require Import Arith.Wf_nat.

Lemma complete_induction_help_compare_1 (A : Type) (a : A) 
(Su : (ℕ → A) → ℕ → A): forall k : nat,
      (complete_induction_help A a Su (S k) k =
      complete_induction_help A a Su (k) k).
Proof.
  intro k.
  simpl.
  destruct (lt_dec k (S k)).
  * reflexivity.
  * assert (H: False) by auto with zarith. 
    destruct H.
Defined.

Lemma complete_induction_help_compare_2 (A : Type) (a : A) 
(Su : (ℕ → A) → ℕ → A): forall k : nat, forall l : nat, (l <= k)%nat -> 
      (complete_induction_help A a Su (S k) l =
      complete_induction_help A a Su (l) l).
      Proof.
  intro k.
  intro l.
  induction k as [|k IHk].
  intro l_le_0.
  assert (l_eq_0 : (l = 0)%nat) by auto with zarith.
  rewrite l_eq_0.
  simpl.
  reflexivity.
  intro l_le_Sk.
  destruct (lt_dec l (S k)).
  rewrite <- IHk.
  simpl.
  destruct (lt_dec l (S (S k))).
  destruct (lt_dec l (S k)).
  reflexivity.
  reflexivity.
  assert (H : False) by auto with zarith.
  destruct H.
  auto with zarith.
  assert (H1 : l = S k) by auto with zarith.
  rewrite H1.
  apply complete_induction_help_compare_1.
Qed.

Lemma complete_induction_help_compare (A : Type) (a : A) 
(Su : (ℕ → A) → ℕ → A): forall k : nat, forall l : nat,
    (l <= k)%nat ->
      (complete_induction_help A a Su k l =
      complete_induction A a Su l).
Proof.
  unfold complete_induction.
  intro k. intro l. intro l_le_k.
  destruct (lt_eq_lt_dec l k) as [Z1 | Z2].
  destruct Z1 as [Z3 | Z4].
  set (m := (k - 1)%nat).
  assert (H : k = S m) by auto with zarith.
  rewrite H.
  apply complete_induction_help_compare_2.
  auto with zarith.
  rewrite Z4.
  reflexivity.
  assert (H : False) by auto with zarith.
  destruct H.
Defined.

Lemma new_induction_principle :  forall A : Type,
  forall P : (nat -> A) -> nat -> Prop,
  (forall f g : nat -> A, forall k : nat, (forall l : nat, (l <= k)%nat -> f l = g l) -> P f k -> P g k) ->
  forall Su : (nat -> A) -> nat -> A,
  forall a : A, forall w : P (fun n : nat => a) 0%nat,
  (forall k : nat,
    (forall l : nat, (l <= k)%nat -> P ((complete_induction_help A a Su) l) l)
    -> P ((complete_induction_help A a Su) (S k)) (S k))
  -> forall k : nat, P (complete_induction A a Su) k.
Proof.
  intros A P H_ext Su a w H_ind.
  intro k.
  apply (H_ext (complete_induction_help A a Su (k)) 
    (complete_induction A a Su)).
  unfold complete_induction.
  apply complete_induction_help_compare.
  induction k as [|k IHk] using complete_induction_prop.
  simpl.
  exact w.
  apply H_ind.
  apply IHk.
Qed.

(* Construct a subsequence with a certain property ... *)

Definition myP (myQ: nat->nat->Prop) (n : nat -> nat) k : Prop :=
  match k with 
  | O => myQ (n O) O
  | S m => ((n k) > n (Nat.pred k))%nat /\ (myQ (n k) k)
  end.

Lemma help_test_1 : forall (myQ: nat->nat->Prop),
forall (f g : ℕ ⇨ ℕ)(l : ℕ),
(for all k : ℕ,
   (k ≤ l)%nat ⇨ f (k) = g (k)) ⇨ myP myQ f l ⇨ myP myQ g l.
Proof.
  intros myQ f g l.
  intro H.
  unfold myP.
  intro myPf.
  destruct l.
  rewrite <- H.
  apply myPf.
  trivial.
  rewrite <- H.
  rewrite <- (H (Nat.pred (S l))).
  apply myPf.
  auto with zarith.
  auto with zarith.
Qed.

(** The next definition captures what it means to be an index sequence.*)
Definition is_index_seq (n : ℕ → ℕ) :=
    ∀ k : ℕ, (n k < n (S k))%nat.
(** Given the function that produces 'good' elements, we can use it to construct a subsequence by induction.*)
Fixpoint create_seq 
  (f : ℕ → ℕ → ℕ) (l : ℕ) :=
  match l with
  | O => f O O
  | S k => f l (S (create_seq f k))
  end.



(** If the function that produces 'good' elements is such that the produced elements are far enough in the sequence, it is certain that the produced sequence is an index sequence.*)
Lemma created_seq_is_index_seq :
  ∀ (g : ℕ → ℕ → ℕ),
    (∀ (m N : ℕ), (g m N ≥ N)%nat ) ⇒
      is_index_seq (create_seq g).
Proof.
    Take g : (ℕ → ℕ → ℕ).
    Assume that (∀ (m N : ℕ), (g m N ≥ N)%nat) (i).
    Expand the definition of is_index_seq.
    That is, write the goal as (for all k : ℕ, (create_seq g k < create_seq g (S k))%nat).
    Take k : ℕ.
    By (i) it holds that (g (S k) (S (create_seq g k)) ≥ S(create_seq g k))%nat.
    We conclude that (& create_seq g k < g (S k) (S (create_seq g k)) = create_seq g (S k))%nat.
Qed.


(** 
The next lemma records that indeed the elements in the subsequence satisfy the desired property.*)
Lemma subseq_sat_rel :
  ∀ (a : ℕ → ℝ) (g : ℕ → ℕ → ℕ) (P : ℕ → ℝ → Prop),
    (∀ m N : ℕ, P m (a (g m N)) ) ⇒ 
      ∀ k : ℕ, P k (a (create_seq g k)).
Proof.
    Take a : (ℕ → ℝ).
    Take g : (ℕ → ℕ → ℕ).
    Take P : (ℕ → ℝ → Prop).
    Assume that (∀ m N : ℕ, P m (a (g m N))) (i).
    induction k. (*TODO: if we use 'We use induction on k.'-tacftic, then we cannot directly match on k + 1 *)
    - We need to show that (P 0%nat (a (g 0%nat 0%nat))).
      By (i) we conclude that (P 0%nat (a (g 0%nat 0%nat))).
    - We need to show that (P (S k) (a (g (S k) (S (create_seq g k))))).
      By (i) we conclude that (P (S k) (a (g (S k) (S (create_seq g k))))).
Qed.

Lemma existence_next_el_to_fun :
    ∀ (a : ℕ → ℝ) (P : ℕ → ℝ → Prop),
    (∀ (m : ℕ) (N : ℕ), ∃ k : ℕ, (N ≤ k)%nat ∧ (P m (a k))) ⇒
      ∃ f : ℕ → ℕ → ℕ, ∀ (m : ℕ) (N : ℕ), (N ≤ f m N)%nat ∧ P m (a (f m N)).
Proof.
    Take a : (ℕ → ℝ). 
    Take P : (ℕ → ℝ → Prop).
    Assume that (for all m N : ℕ, there exists k : ℕ , (N ≤ k)%nat ∧ P m (a k)) (i).
    We claim that (∀ (m : ℕ),  ∃ g : ℕ → ℕ, ∀ N : ℕ, (N ≤ g N)%nat ∧ (P m (a (g N)))) (ii).
    {
        Take m : ℕ.
        apply choice with (R := fun (k : ℕ) (l : ℕ) ↦ ((k ≤ l)%nat ∧ P m (a l))).
        By (i) we conclude that (for all x : ℕ, there exists y : ℕ, (x ≤ y)%nat ∧ P m (a y)).
    }
    apply choice with (R := fun (m : ℕ) (h : ℕ → ℕ) ↦ ( ∀ N : ℕ, (N ≤ h N)%nat ∧ P m (a (h N)) ) ).
    By (ii) we conclude that (for all x : ℕ, there exists y : ℕ ⇨ ℕ , for all N : ℕ, (N ≤ y N)%nat ∧ P x (a (y N))).
Qed.

Lemma exists_good_subseq :
  ∀ (a : ℕ → ℝ) (P : ℕ → ℝ → Prop),
    (∀ (m : ℕ) (N : ℕ), ∃ k : ℕ, (N ≤ k)%nat ∧ (P m (a k))) ⇒
      ∃ n : ℕ → ℕ, is_index_seq n ∧ ∀ k : ℕ, P k (a (n k)).
Proof.
    Take a : (ℕ → ℝ).
    Take P : (ℕ → ℝ → Prop).
    Assume that (for all m N : ℕ, there exists k : ℕ , (N ≤ k)%nat ∧ P m (a k)).
    By existence_next_el_to_fun it holds that
      (∃ g : ℕ → ℕ → ℕ, ∀ (m : ℕ) (N : ℕ), (N ≤ g m N)%nat ∧ P m (a (g m N))).
    Obtain such a g. It holds that
      (∀ (m : ℕ) (N : ℕ), (N ≤ g m N)%nat ∧ P m (a (g m N))) (ii).
    Choose n := (create_seq g).
    We show both statements.
    - We need to show that (is_index_seq n).
      We need to show that (is_index_seq (create_seq g)).
      By created_seq_is_index_seq it suffices to show that 
        (for all m N : ℕ, (g m N ≥ N)%nat).
      Take m, M : nat.
      By (ii) it holds that ((M ≤ g m M)%nat ∧ P m (a (g m M))).
      We conclude that (M <= g m M)%nat.
    - We need to show that (for all k : ℕ, P k (a (n k))).
      We need to show that (for all k : ℕ, P k (a ((create_seq g) k))).
      Fail By subseq_sat_rel it suffices to show that (for all m N : ℕ, P m (a (g m N))). (*TODO: fix*)
      apply subseq_sat_rel.
      Take m : ℕ.
      Take M : ℕ.
      By (ii) it holds that ((M ≤ g m M)%nat ∧ P m (a (g m M))) (iii).
      Because (iii) both (M ≤ g m M)%nat and (P m (a (g m M))) hold.
      We conclude that (P m (a (g m M))).
Qed.


Definition is_increasing (f : ℕ → ℕ) :=
  ∀ k : ℕ, (f k ≤ f (S k))%nat.
Lemma incr_loc_to_glob :
  ∀ g : ℕ → ℕ,
    is_increasing g
      ⇒ (∀ k l : ℕ, (k ≤ l)%nat ⇒ (g k ≤ g l)%nat).
Proof.
    Take g : (ℕ → ℕ). 
    Expand the definition of is_increasing.
    That is, write the goal as ((for all k : ℕ, (g k ≤ g (S k))%nat) 
      ⇨ for all k l : ℕ, (k ≤ l)%nat ⇨ (g k ≤ g l)%nat).
    Assume that (∀ k : ℕ, (g k ≤ g (S k))%nat).
    Take k : ℕ. 
    induction l as [|l IH_l].

    (** We first need to show that if $k \leq 0$ then $(f (k) \leq f(0))$.*)
    Assume that (k ≤ 0)%nat.
    It holds that (k = 0)%nat.
    We conclude that (& g k = g 0 <= g 0)%nat.

    (** Next, we need to show that if $k \leq S (l)$ then $f(k) \leq f(S (l))$.*)
    Assume that (k ≤ S l)%nat.
    destruct (lt_eq_lt_dec k (S l)) as [temp | k_gt_Sl].
    destruct temp as [k_lt_Sl | k_eq_Sl].
    (** We first consider the case that $k < S(l)$.*)
    It holds that (k ≤ l)%nat.
    By IH_l it holds that (g k ≤ g l)%nat.
    It holds that (g l ≤ g (S l))%nat.
    We conclude that (g k <= g (S l))%nat.
    (** We now consider the case $k = S(l)$. We need to show that $f(k) \leq f(S(l))$. *)
    We conclude that (& g k = g (S l) <= g (S l))%nat.
    (** Finally we consider the case $k > S(l)$. However, this case is in contradiction with $k \leq S(l)$. *)
    It holds that (¬(S l < k)%nat).
    Contradiction.
Qed.


Lemma index_seq_strictly_incr :
  ∀ n : ℕ → ℕ, is_index_seq n ⇒ (is_increasing (fun (k : ℕ) ↦ (n k - k)%nat)).
Proof.
    Take n : (ℕ → ℕ); such that (is_index_seq n) (i).
    Expand the definition of is_increasing.
    That is, write the goal as (for all k : ℕ, (n k - k ≤ n (S k) - S k)%nat).
    Take k : ℕ.
    Expand the definition of is_index_seq in (i).
    That is, write (i) as (for all k0 : ℕ, (n k0 < n (S k0))%nat).
    It holds that (n k < n (S k))%nat.
    We conclude that (n k - k ≤ n (S k) - S k)%nat.
Qed.

Lemma index_seq_grows_0 :
  ∀ n : ℕ → ℕ, is_index_seq n ⇒ ∀ k : ℕ, (n k ≥ k)%nat.
Proof.
    Take n : (ℕ → ℕ); such that (is_index_seq n) (i).
    induction k as [|k IH].
    - We conclude that (n 0 >= 0)%nat.
    - Expand the definition of is_index_seq in (i).
      That is, write (i) as (for all k0 : ℕ, (n k0 < n (S k0))%nat).
      It holds that (n k < n (S k))%nat.
      We conclude that (n (S k) ≥ S k)%nat.
Qed.

Lemma index_seq_grows :
  ∀ n : ℕ → ℕ, is_index_seq n ⇒ (∀ k l : ℕ, (k ≤ l)%nat ⇒ (n k - k ≤ n l - l)%nat).
Proof.
    Take n : (ℕ → ℕ); such that (is_index_seq n).
    Define g := (fun (k : ℕ) ↦ (n k - k)%nat).
    By index_seq_strictly_incr it holds that (is_increasing g).
    By incr_loc_to_glob it holds that (∀ k l : ℕ, (k ≤ l)%nat ⇒ (g k ≤ g l)%nat).
    Take k : ℕ and l : ℕ; such that(k ≤ l)%nat.
    We need to show that (g k <= g l)%nat.
    We conclude that (g k <= g l)%nat.
Qed.



(** ## Constructing a subsequence with elements satisfying a particular property

Given a property $P : \mathbb{N} → \mathbb{R} → \mathrm{Prop}$, and given that it holds for infinitely many elements in the sequence, we want to find a subsequence with all elements satisfying the property. *)
(** ### Finding the smallest element satisfying the property

This seems to require some decidability on the property*)
Fixpoint first_satisfying_element_helper
  (rel : ℕ → ℕ → bool)
  (k : ℕ)
  (N : ℕ) :=
  match k with
  | O => N
  | S l => if (rel (N-k)%nat (N-k)%nat) 
                then k
                else (first_satisfying_element_helper rel l N)
  end.  
Definition first_satisfying_element
  (rel : ℕ → ℕ → bool)
  (l : ℕ)
  (N : ℕ)
  := first_satisfying_element_helper rel (N-l) N.  
(** ### From infinitely many elements to a function producing those elements*)
Lemma inf_el_to_fun :
  ∀ (a : ℕ → ℝ) (P : ℕ → ℝ → Prop),
    (∀ N : ℕ, ∃ k : ℕ, (N ≤ k)%nat ∧ (P N (a k))) ⇒
      ∃ f : ℕ → ℕ, ∀ l : ℕ, (l ≤ f l)%nat ∧ P l (a (f l)).
Proof.
    Take a : (ℕ → ℝ). 
    Take P : (ℕ → ℝ → Prop).
    apply choice with (R := fun (k : ℕ) (l : ℕ) ↦ ((k ≤ l)%nat ∧ P k (a l))).
Qed.


Fixpoint seq_of_max (f : ℕ → ℕ) (l : ℕ) :=
  match l with 
  | O => f O
  | S k => Nat.max (f l) (seq_of_max f k)
  end.


(** ### The sequence of maxima is increasing*)
Lemma seq_of_max_is_increasing :
  ∀ g : ℕ → ℕ, is_increasing (seq_of_max g).
Proof.
    Take g : (ℕ → ℕ).
    Expand the definition of is_increasing.
    That is, write the goal as (for all k : ℕ, (seq_of_max g k ≤ seq_of_max g (S k))%nat).
    Take k : ℕ.
    We need to show that (seq_of_max g k ≤ Nat.max (g (S k)) (seq_of_max g k))%nat.
    We conclude that (seq_of_max g k ≤ Nat.max (g (S k)) (seq_of_max g k))%nat.
Qed.


Lemma elements_le_seq_of_max_pre :
  ∀ (g : ℕ → ℕ) (n : ℕ),
    (g n ≤ seq_of_max g n)%nat.
Proof.
    Take g : (ℕ → ℕ).
    induction n as [|n IH_n].
    (** We first consider the base case $n=0$.*)
    Expand the definition of seq_of_max.
    That is, write the goal as ((g 0 ≤ g 0)%nat).
    (** We need to show that $f( 0 ) \leq f( 0)$.*)
    We conclude that (g 0 ≤ g 0)%nat.
    (** Next we consider the general case. We need to show that $f(S(n))\leq \mathsf{seqofmax}(f, S(n))$. *)
    Expand the definition of seq_of_max.
    That is, write the goal as ((g (S n) ≤ Nat.max (g (S n))
     ((fix seq_of_max (f : ℕ ⇨ ℕ) (l : ℕ) {struct l} : ℕ :=
         match l with
         | 0 => f 0
         | S k => Nat.max (f l) (seq_of_max f k)
         end) g n))%nat).
    (** By the definition of $\mathsf{seqofmax}(f,S(n))$ as the maximum of $f(S(n))$ and another number, this*)
    We conclude that (g (S n) ≤ Nat.max (g (S n))
     ((fix seq_of_max (f : ℕ ⇨ ℕ) (l : ℕ) {struct l} : ℕ :=
         match l with
         | 0 => f 0
         | S k => Nat.max (f l) (seq_of_max f k)
         end) g n))%nat.
Qed.

Lemma elements_le_seq_of_max :
  ∀ (g : ℕ → ℕ) (n : ℕ) (k : ℕ),
    (k ≤ n)%nat ⇒ (g k ≤ seq_of_max g n)%nat.
Proof.
  Take g : (ℕ → ℕ).
  Take n : ℕ and k : ℕ; such that (k ≤ n)%nat.
  By elements_le_seq_of_max_pre it holds that (g k ≤ seq_of_max g k)%nat.
  We claim that (seq_of_max g k ≤ seq_of_max g n)%nat.
  { By incr_loc_to_glob it suffices to show that (is_increasing (seq_of_max g)).
    By seq_of_max_is_increasing we conclude that (is_increasing (seq_of_max g)).
  }
  We conclude that (& g k <= seq_of_max g k <= seq_of_max g n)%nat.
Qed.


(** ### From a function producing the correct elements to an index sequence*)
Fixpoint build_seq 
  (f : ℕ → ℕ) 
  (k : ℕ) :=
  match k with 
  | O => f O
  | S m => f (S (seq_of_max f (build_seq f m)))
  end.
Lemma built_seq_is_index_seq :
  ∀ g : ℕ → ℕ,
    (∀ k : ℕ, (g k ≥ k)%nat) ⇒
      is_index_seq (build_seq g).
Proof.
  Take g : (ℕ → ℕ).
  Assume that (for all k : ℕ, (g k ≥ k)%nat).
  Expand the definition of is_index_seq.
  That is, write the goal as (for all k : ℕ, (build_seq g k < build_seq g (S k))%nat).
  Take k : ℕ.
  We need to show that (build_seq g k < g (S (seq_of_max g (build_seq g k))))%nat.
  It holds that (g( S(seq_of_max g (build_seq g k)))≥ S(seq_of_max g (build_seq g k)))%nat.
  It holds that (g( S(seq_of_max g (build_seq g k)))> seq_of_max g (build_seq g k))%nat.
  By elements_le_seq_of_max_pre it holds that (seq_of_max g (build_seq g k) ≥ g(build_seq g k))%nat.
  It holds that (g(build_seq g k) ≥ build_seq g k)%nat.
  We conclude that (& build_seq g k <= g(build_seq g k)
                                    <= seq_of_max g (build_seq g k)
                                    <  g( S(seq_of_max g (build_seq g k))))%nat.
Qed.
(** ### Subsequence satisfies relation*)
