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

Require Import Waterproof.Waterproof.
From Stdlib Require Import Lia.
From Stdlib Require Import Arith.
From Stdlib Require Import Arith.Compare.
From Stdlib Require Import ClassicalChoice.
From Stdlib Require Import ChoiceFacts.

Require Import Notations.Sets.
Require Import Libs.Analysis.SubsequencesMetric.

Section Construction.

Definition dep_only_on_start {A : Type} (P : nat -> (nat -> A) -> Prop)
  := forall (k : nat) (b c : nat -> A), (forall l : nat, l <= k -> b l = c l) -> (P k b) -> (P k c).

Definition const_seq {A : Type} (a : A) := (fun l : nat => a).
Definition const_seq_from {A : Type} (a : A) (k : nat) (seq : nat -> A) :=
  fun l : nat => if (lt_dec l k) then (seq l) else a.


Context {A : Type} {P : nat -> (nat -> A) -> Prop} (HypP : dep_only_on_start P).
Context (a0 : A) (H0 : P 0 (const_seq a0))
  (Hstep : forall (k : nat) (prev : nat -> A),
    P k prev -> {a : A | P (S k) (const_seq_from a (S k) prev)}).


Fixpoint ind_seq_of_seq_and_prop (k : nat) : {seq : nat -> A | P k seq} :=
  match k with
  | O   => exist _ (const_seq a0) H0
  | S k => exist _ (const_seq_from
                     (proj1_sig (Hstep _ _ (proj2_sig (ind_seq_of_seq_and_prop k))))
                     (S k) (proj1_sig (ind_seq_of_seq_and_prop k)))
                   (proj2_sig (Hstep _ _ (proj2_sig (ind_seq_of_seq_and_prop k))))
  end.


Definition ind_seq_with_prop : {seq : nat -> A | forall k : nat, P k seq}.
Proof.
  ltac2: set ind_seq_of_seq_and_prop as seq_of_seq.
  ltac2: exists (fun k => proj1_sig (seq_of_seq k) k). (* take the diagonal *)
  ltac2: intro k.
  ltac2: apply (HypP _ (proj1_sig (seq_of_seq k))).
  - (* k-th sequence matches diagonal sequence for first k terms *)
    ltac2: intros l Hl.
    ltac2: induction k.
    + ltac2: (assert (l = 0) as l_eq_0 by ltac1: (lia)). (* l <= 0 implies l = 0 *)
      ltac2: (rewrite l_eq_0; reflexivity).
    + ltac2: (simpl; unfold const_seq_from).
      ltac2: destruct (lt_dec l (S k)) as [l_lt_Sk | not_l_lt_Sk].
      * ltac2: (apply IHk; ltac1: (lia)).
      * ltac2: assert (l = S k) as l_eq_Sk by ltac1: (lia).
        ltac2: rewrite l_eq_Sk.
        ltac2: (simpl; unfold const_seq_from).
        ltac2: destruct (lt_dec (S k) (S k)) as [Sk_lt_Sk | not_Sk_lt_Sk].
        -- ltac2: (assert (con : False) by ltac1:(lia); ltac1:(contradiction)).
        -- ltac2: reflexivity.
  - (* k-th sequence satisfies k-th property *)
    ltac2: exact (proj2_sig (seq_of_seq k)).
Defined.

End Construction.



Section StrongInduction.

Lemma quant_over_start_dep_only_on_start {A : Type} {P : nat -> (nat -> A) -> Prop} :
  dep_only_on_start P -> dep_only_on_start (fun (k : nat) (seq : nat -> A) => forall l : nat, l <= k -> P l seq).
Proof.
  ltac2: intros HypP k b c start_b_eq_c Hb l l_le_k.
  ltac2: apply (HypP _ b).
  - ltac2: intros i i_le_l.
    ltac2: (apply start_b_eq_c; ltac1:(lia)).
  - ltac2: (apply Hb; assumption).
Qed.

Lemma reformulate_base_prop_strong {A : Type} (P : nat -> (nat -> A) -> Prop) (seq : nat -> A) :
  (P 0 seq) -> (forall l : nat, l <= 0 -> P l seq).
Proof.
  ltac2: intros H0 l l_le_0.
  ltac2: assert (l = 0) as l_eq_0 by ltac1:(lia).
  ltac2: (rewrite l_eq_0; exact H0).
Qed.

Lemma reformulate_final_prop_strong {A : Type} (P : nat -> (nat -> A) -> Prop) (seq : nat -> A) :
  (forall k : nat, forall l : nat, l <= k -> P l seq) -> (forall k : nat, P k seq).
Proof.
  ltac2: intros H k.
  ltac2: assert (k <= k) as k_le_k by ltac1:(lia).
  ltac2: exact (H k k k_le_k).
Qed.


Theorem strong_ind_seq_with_prop {A : Type} {P : nat -> (nat -> A) -> Prop} (HypP : dep_only_on_start P)
  (a0 : A) (H0 : P 0 (const_seq a0))
  (Hstep : forall (k : nat) (prev : nat -> A),
    (forall l : nat, l <= k -> P l prev) -> {a : A | forall l : nat, l <= (S k) -> P l (const_seq_from a (S k) prev)})
  : {seq : nat -> A | forall k : nat, P k seq}.
Proof.
  ltac2: enough {seq : nat -> A | forall k : nat, forall l : nat, l <= k -> P l seq} as [seq Hseq].
  { ltac2: exists seq.
    ltac2: (apply reformulate_final_prop_strong; exact Hseq).
  }
  ltac2: apply (ind_seq_with_prop (quant_over_start_dep_only_on_start HypP) a0).
  - ltac2: (apply reformulate_base_prop_strong; exact H0).
  - ltac2: exact Hstep.
Defined.

End StrongInduction.



Section StrongInductionIndexSequence.

(* Definition is_index_seq (n : nat -> nat) := forall k : nat, n (k + 1) > n k. *)

Definition index_seq_prop_family (Q : nat -> Prop) (k : nat) (n : nat -> nat) :=
  match k with
  | O   => Q (n 0)
  | S k => Q (n (k + 1)) /\ n k < n (k + 1)
  end.

Lemma dep_only_on_start_index_seq_prop_family (Q : nat -> Prop) :
  dep_only_on_start (index_seq_prop_family Q).
Proof.
  ltac2: intros k b c b_eq_c_start Hb.
  ltac2: induction k.
  - ltac2: simpl.
    ltac2: assert (0 <= 0) as O_le_O by ltac1:(lia).
    ltac2: rewrite <- (b_eq_c_start 0 O_le_O).
    ltac2: exact Hb.
  - ltac2: simpl.
    ltac2: assert (k + 1 <= S k) as kplus1_le_Sk by ltac1:(lia).
    ltac2: rewrite <- (b_eq_c_start (k + 1) kplus1_le_Sk).
    ltac2: assert (k <= S k) as k_le_Sk by ltac1:(lia).
    ltac2: rewrite <- (b_eq_c_start k k_le_Sk).
    ltac2: exact Hb.
Qed.


Lemma reformulate_base_prop_index {Q : nat -> Prop} (n : nat -> nat) (k : nat) :
  Q k -> index_seq_prop_family Q 0 (const_seq k).
Proof.
  ltac2: intro Hk.
  ltac2: simpl. 
  ltac2: unfold const_seq.
  ltac2: exact Hk.
Qed.


Lemma reformulate_final_prop_index {Q : nat -> Prop} {n : nat -> nat} :
  (forall k : nat, index_seq_prop_family Q k n) -> is_index_seq n /\ forall k : nat, Q (n k).
Proof.
  ltac2: intro H.
  ltac2: split.
  - ltac2: intros k Hk.
    ltac2: exact (proj2 (H (S k))).
  - ltac2: induction k.
    + ltac2: exact (H O).
    + ltac2: (assert (S k = k + 1) as Sk_eq_kplus1 by ltac1:(lia); rewrite Sk_eq_kplus1).
      ltac2: exact (proj1 (H (S k))).
Qed.

Lemma reformulate_step_prop_index {Q : nat -> Prop} :
  (forall (k : nat) (n : nat -> nat),
    (forall l : nat, l <= k -> Q (n l)) -> (forall l : nat, l < k -> n l < n (l + 1)) ->
    {n_kplus1 : nat | Q n_kplus1 /\ n k < n_kplus1})
    ->
  (forall (k : nat) (n : nat -> nat),
    (forall l : nat, l <= k -> index_seq_prop_family Q l n) ->
    {n_kplus1 : nat | forall l : nat, l <= k + 1 -> index_seq_prop_family Q l (const_seq_from n_kplus1 (k + 1) n)}).
Proof.
  ltac2: intros Hstep k n H.
  ltac2: assert (forall l : nat, l <= k -> Q (n l)) as H1.
  { ltac2: intros l le_k.
    ltac2: induction l.
    - ltac2: apply (H 0 le_k).
    - ltac2: (assert (S l = l + 1) as Sl_eq_lplus1 by ltac1:(lia); rewrite Sl_eq_lplus1).
      ltac2: apply (proj1 (H (S l) le_k)).
  }
  ltac2: assert (forall l : nat, l < k -> n l < n (l + 1)) as H2.
  { ltac2: intros l lt_k.
    ltac2: apply (proj2 (H (S l) lt_k)).
  }
  ltac2: destruct (Hstep k n H1 H2) as [n_kplus1 Hn_kplus1].
  ltac2: exists n_kplus1.
  ltac2: intros l le_kplus1.
  ltac2: induction l.
  - ltac2: (simpl; unfold const_seq_from).
    ltac2: destruct (lt_dec 0 (k + 1)) as [O_lt_kplus1 | not_O_lt_kplus1].
    + ltac2: (assert (0 <= k) as O_le_k by ltac1:(lia)).
      ltac2: exact (H1 0 O_le_k).
    + ltac2: exact (proj1 Hn_kplus1).
  - ltac2:(simpl; unfold const_seq_from).
    ltac2: destruct (lt_dec (l + 1) (k + 1)) as [lplus1_lt_kplus1 | not_lplus1_lt_kplus1].
    + ltac2: split.
      * ltac2: assert (l + 1 <= k) as lplus1_le_k by ltac1:(lia).
        ltac2: exact (H1 (l + 1) lplus1_le_k).
      * ltac2: destruct (lt_dec l (k + 1)) as [l_lt_kplus1 | not_l_lt_kplus1].
        -- ltac2: assert (S l <= k) as Sl_le_k by ltac1:(lia).
           ltac2: exact (proj2 (H (S l) Sl_le_k)).
        -- ltac2: (assert False by ltac1:(lia); ltac1:(contradiction)).
    + ltac2: split.
      * ltac2: exact (proj1 Hn_kplus1).
      * ltac2: destruct (lt_dec l (k + 1)) as [l_lt_kplus1 | not_l_lt_kplus1].
        -- ltac2: assert (l = k) as l_eq_k by ltac1:(lia).
           ltac2: rewrite l_eq_k.
           ltac2: exact (proj2 Hn_kplus1).
        -- ltac2: (assert False by ltac1:(lia); ltac1:(contradiction)).
Qed.


Theorem strong_ind_index_seq_with_prop {Q : nat -> Prop}
  (H0 : {n_0 : nat | Q n_0})
  (Hstep : forall (k : nat) (n : nat -> nat),
    (forall l : nat, l <= k -> Q (n l)) -> (forall l : nat, l < k -> n l < n (l + 1)) ->
    {n_kplus1 : nat | Q n_kplus1 /\ n k < n_kplus1})
  : {n : nat -> nat | is_index_seq n /\ forall k : nat, Q (n k)}.
Proof.
  ltac2: enough {n : nat -> nat | forall k : nat, index_seq_prop_family Q k n} as [n Hn].
  { ltac2: exists n.
    ltac2: apply reformulate_final_prop_index.
    ltac2: exact Hn.
  }
  ltac2: destruct H0 as [n0 Hn0].
  ltac2: apply (strong_ind_seq_with_prop (dep_only_on_start_index_seq_prop_family Q) n0).
  - ltac2: apply (reformulate_base_prop_index (const_seq n0)).
    ltac2: exact Hn0.
  - ltac2: intro k.
    ltac2: (assert (S k = k + 1) as Sk_eq_kplus1 by ltac1:(lia); rewrite Sk_eq_kplus1).
    ltac2: apply reformulate_step_prop_index.
    ltac2: apply Hstep.
Qed.


Definition dep_choice := non_dep_dep_functional_choice choice.

Lemma help_with_choice {A B C : Type} {D E : A -> B -> Prop} {P : A -> B -> C -> Prop} :
  (forall (a : A) (b : B), D a b -> E a b-> exists c : C, P a b c) ->
  (exists f : forall (a : A) (b : B), D a b -> E a b -> C, forall (a : A) (b : B) (d : D a b) (e : E a b), P a b (f a b d e)).
Proof.
  ltac2: intro H.
  ltac2: apply (dep_choice _ _ (fun a f => forall (b : B) (d : D a b) (e : E a b), P a b (f b d e))).
  ltac2: intro a.
  ltac2: apply (dep_choice _ _ (fun b f => forall (d : D a b) (e : E a b), P a b (f d e))).
  ltac2: intro b.
  ltac2: apply (choice (fun d f => forall (e : E a b), P a b (f e))).
  ltac2: intro d.
  ltac2: apply (choice (fun e c => P a b c)).
  ltac2: apply (H a b d).
Qed.

Theorem classic_strong_ind_index_seq_with_prop {Q : nat -> Prop}
  (H0 : exists n_0 : nat, Q n_0)
  (Hstep : forall (k : nat) (n : nat -> nat),
    (forall l : nat, l <= k -> Q (n l)) -> (forall l : nat, l < k -> n l < n (l + 1)) ->
    exists n_kplus1 : nat, Q n_kplus1 /\ n k < n_kplus1)
  : exists n : nat -> nat, is_index_seq n /\ forall k : nat, Q (n k).
Proof.
  ltac2: destruct H0 as [n0 Hn0].
  ltac2: assert {n0 | Q n0} as H0sig by (exists n0; exact Hn0).
  (* Transform Hstep using choice such that the existence statement is at the start so it can be destructed. *)
  ltac2: pose (help_with_choice Hstep) as Hstep2.
  ltac2: destruct Hstep2 as [f Hf].
  (* Use strong version to prove existence statement. *)
  ltac2: enough {n : nat -> nat | is_index_seq n /\ (forall k : nat, Q (n k))} as [n Hn].
  { ltac2: (exists n; exact Hn). }
  ltac2: apply (strong_ind_index_seq_with_prop H0sig).
  (* Use transformed Hstep to prove strong Hstep condition. *)
  ltac2: intros k n H1 H2.
  ltac2: exists (f k n H1 H2).
  ltac2: apply Hf.
Qed.

Open Scope subset_scope.

Theorem classic_strong_ind_index_seq_with_prop_with_element_notation {Q : nat -> Prop}
  (H0 : ∃ n_0 ∈ nat, Q n_0)
  (Hstep : forall (k : nat) (n : nat -> nat),
    (∀ l ≤ k, Q (n l)) -> (∀ l < k, n l < n (l + 1)) ->
    ∃ n_kplus1 ∈ nat, Q n_kplus1 /\ n k < n_kplus1)
  : ∃ n index sequence, ∀ k ∈ nat, Q (n k).
Proof.
  ltac2: enough (exists n : nat -> nat, is_index_seq n /\ forall k : nat, Q (n k)) as H.
  + ltac2: destruct H as [n0 Hn0].
    ltac2: exists n0.
    ltac2: split.
      * ltac2: exact (proj1 Hn0).
      * ltac2: intros k Hk.
        ltac2: apply (proj2 Hn0).
  + ltac2: apply classic_strong_ind_index_seq_with_prop.
    - ltac2: destruct H0 as [n0 Hn0].
      ltac2: exists n0.
      ltac2: exact (proj2 Hn0).
    - ltac2: intros k n H1 H2.
      ltac2: enough ( ∃ n_kplus1 ∈ nat, Q n_kplus1 /\ n k < n_kplus1) as H.
      * ltac2: destruct H as [n_kplus1 Hn_kplus1].
        ltac2: exists n_kplus1.
        ltac2: exact (proj2 Hn_kplus1).
      * ltac2: apply Hstep.
        ++ ltac2: intros l Hl. 
           ltac2: unfold le_op, nat_le_type in Hl. 
           ltac2: (apply H1; assumption).
        ++ ltac2: intros l Hl. 
           ltac2: unfold lt_op, nat_lt_type in Hl. 
           ltac2: (apply H2; assumption).
Qed.

End StrongInductionIndexSequence.


(** Tactics  *)
(** Warning: we don't (yet) know how to specify dummy variables in existence statements,
  so the use of the letters 'n' and 'k' in the tactics is hard-coded.  *)

Require Import Waterproof.
Require Import Ltac2.Message.

Local Ltac2 concat_list (ls : message list) : message :=
  List.fold_right concat ls (of_string "").

Require Import Waterproof.Util.Goals.
Require Import Util.MessagesToUser.

Open Scope subset_scope.

Local Ltac2 inductive_def_index_seq_n () :=
  let apply_induction_principle (p : constr) :=
    let q := eval unfold id in (fun l : nat => $p id l) in
    match Control.case (fun () => apply (@classic_strong_ind_index_seq_with_prop_with_element_notation $q)) with
    | Val _ =>
      Control.focus 1 1 (fun () => apply StrongIndIndxSeq.Base.unwrap);
      Control.focus 2 2 (fun () => apply StrongIndIndxSeq.Step.unwrap)
    | Err _ => throw (of_string "The index sequence cannot be defined using this technique.")
    end in
  lazy_match! goal with
  | [ |- ∃ n : nat -> nat, is_index_sequence n /\ ∀ k ∈ conv nat, @?p n k] => (*@?p*) apply_induction_principle p
  | [ |- ∃ n index sequence, ∀ k ∈ conv nat, @?p n k] => (*@?p*)
    apply_induction_principle p
  | [ |- _ ] => throw (of_string "The goal is not to define an index sequence.")
  end.

Ltac2 Notation "Define" "the" "index" "sequence" "n" "inductively" :=
  panic_if_goal_wrapped ();
  inductive_def_index_seq_n ().

Local Ltac2 take_first_k () :=
  lazy_match! goal with
  | [|- StrongIndIndxSeq.Step.Wrapper _] => apply StrongIndIndxSeq.Step.wrap; intros k n
  | [|- _] => throw (of_string "No need to introduce first k elements of sequence n.")
  end.

Local Ltac2 strong_ind_indx_base () :=
  lazy_match! goal with
  | [|- StrongIndIndxSeq.Base.Wrapper _] => apply StrongIndIndxSeq.Base.wrap
  | [|- _] => throw (of_string "No need to define n_0.")
  end.

Ltac2 Notation "We" "first" "define" "n_0" :=
  strong_ind_indx_base ().

Ltac2 Notation "Take" "k" "∈" "ℕ" "and" "assume" "n_0,...,n_k" "are" "defined" :=
  take_first_k ().
