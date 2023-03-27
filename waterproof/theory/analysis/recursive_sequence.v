Require Import Lia.
Require Import Arith.
Require Import Arith.Compare.
Require Import ClassicalChoice.
Require Import ChoiceFacts.


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


Fixpoint rec_seq_of_seq_and_prop (k : nat) : {seq : nat -> A | P k seq} :=
  match k with
  | O   => exist _ (const_seq a0) H0
  | S k => exist _ (const_seq_from 
                     (proj1_sig (Hstep _ _ (proj2_sig (rec_seq_of_seq_and_prop k))))
                     (S k) (proj1_sig (rec_seq_of_seq_and_prop k)))
                   (proj2_sig (Hstep _ _ (proj2_sig (rec_seq_of_seq_and_prop k))))
  end.


Definition rec_seq_with_prop : {seq : nat -> A | forall k : nat, P k seq}.
Proof.
  set rec_seq_of_seq_and_prop as seq_of_seq.
  exists (fun k => proj1_sig (seq_of_seq k) k). (* take the diagonal *)
  intro k.
  apply (HypP _ (proj1_sig (seq_of_seq k))).
  - (* k-th sequence matches diagonal sequence for first k terms *)
    intros l Hl.
    induction k.
    + assert (l = 0) as l_eq_0 by lia. (* l <= 0 implies l = 0 *)
      rewrite l_eq_0; reflexivity.
    + simpl; unfold const_seq_from.
      destruct (lt_dec l (S k)) as [l_lt_Sk | not_l_lt_Sk].
      * apply IHk; lia.
      * assert (l = S k) as l_eq_Sk by lia.
        rewrite l_eq_Sk.
        simpl; unfold const_seq_from.
        destruct (lt_dec (S k) (S k)) as [Sk_lt_Sk | not_Sk_lt_Sk].
        -- assert (con : False) by lia; contradiction.
        -- reflexivity.
  - (* k-th sequence satisfies k-th property *)
    exact (proj2_sig (seq_of_seq k)).
Defined.

End Construction.



Section FullRecursion.

Lemma quant_over_start_dep_only_on_start {A : Type} {P : nat -> (nat -> A) -> Prop} : 
  dep_only_on_start P -> dep_only_on_start (fun (k : nat) (seq : nat -> A) => forall l : nat, l <= k -> P l seq).
Proof.
  intros HypP k b c start_b_eq_c Hb l l_le_k.
  apply (HypP _ b).
  - intros i i_le_l.
    apply start_b_eq_c; lia.
  - apply Hb; assumption.
Qed.

Lemma reformulate_base_prop_full {A : Type} (P : nat -> (nat -> A) -> Prop) (seq : nat -> A) :
  (P 0 seq) -> (forall l : nat, l <= 0 -> P l seq).
Proof.
  intros H0 l l_le_0.
  assert (l = 0) as l_eq_0 by lia.
  rewrite l_eq_0; exact H0.
Qed.

Lemma reformulate_final_prop_full {A : Type} (P : nat -> (nat -> A) -> Prop) (seq : nat -> A) :
  (forall k : nat, forall l : nat, l <= k -> P l seq) -> (forall k : nat, P k seq).
Proof.
  intros H k.
  assert (k <= k) as k_le_k by lia.
  exact (H k k k_le_k).
Qed.


Theorem full_rec_seq_with_prop {A : Type} {P : nat -> (nat -> A) -> Prop} (HypP : dep_only_on_start P)
  (a0 : A) (H0 : P 0 (const_seq a0))
  (Hstep : forall (k : nat) (prev : nat -> A),
    (forall l : nat, l <= k -> P l prev) -> {a : A | forall l : nat, l <= (S k) -> P l (const_seq_from a (S k) prev)})
  : {seq : nat -> A | forall k : nat, P k seq}.
Proof.
  enough {seq : nat -> A | forall k : nat, forall l : nat, l <= k -> P l seq} as [seq Hseq].
  { exists seq.
    apply reformulate_final_prop_full; exact Hseq.
  }
  apply (rec_seq_with_prop (quant_over_start_dep_only_on_start HypP) a0).
  - apply reformulate_base_prop_full; exact H0.
  - exact Hstep.
Defined.

End FullRecursion.



Section FullRecursiveIndexSequence.

Definition is_index_seq (n : nat -> nat) := forall k : nat, n (k + 1) > n k.

Definition index_seq_prop_family (Q : nat -> Prop) (k : nat) (n : nat -> nat) := 
  match k with 
  | O   => Q (n 0)
  | S k => Q (n (k + 1)) /\ n k < n (k + 1)
  end.

Lemma dep_only_on_start_index_seq_prop_family (Q : nat -> Prop) :
  dep_only_on_start (index_seq_prop_family Q).
Proof.
  intros k b c b_eq_c_start Hb.
  induction k.
  - simpl.
    assert (0 <= 0) as O_le_O by lia.
    rewrite <- (b_eq_c_start 0 O_le_O).
    exact Hb.
  - simpl.
    assert (k + 1 <= S k) as kplus1_le_Sk by lia.
    rewrite <- (b_eq_c_start (k + 1) kplus1_le_Sk).
    assert (k <= S k) as k_le_Sk by lia.
    rewrite <- (b_eq_c_start k k_le_Sk).
    exact Hb.
Qed.


Lemma reformulate_base_prop_index {Q : nat -> Prop} (n : nat -> nat) (k : nat) :
  Q k -> index_seq_prop_family Q 0 (const_seq k).
Proof.
  intro Hk.
  simpl. unfold const_seq.
  exact Hk.
Qed.


Lemma reformulate_final_prop_index {Q : nat -> Prop} {n : nat -> nat} :
  (forall k : nat, index_seq_prop_family Q k n) -> is_index_seq n /\ forall k : nat, Q (n k).
Proof.
  intro H.
  split.
  - intro k.
    exact (proj2 (H (S k))).
  - induction k.
    + exact (H O).
    + assert (S k = k + 1) as Sk_eq_kplus1 by lia; rewrite Sk_eq_kplus1.
      exact (proj1 (H (S k))).
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
  intros Hstep k n H.
  assert (forall l : nat, l <= k -> Q (n l)) as H1.
  { intros l le_k.
    induction l.
    - apply (H 0 le_k).
    - assert (S l = l + 1) as Sl_eq_lplus1 by lia; rewrite Sl_eq_lplus1.
      apply (proj1 (H (S l) le_k)).
  }
  assert (forall l : nat, l < k -> n l < n (l + 1)) as H2.
  { intros l lt_k.
    apply (proj2 (H (S l) lt_k)).
  }
  destruct (Hstep k n H1 H2) as [n_kplus1 Hn_kplus1].
  exists n_kplus1.
  intros l le_kplus1.
  induction l.
  - simpl; unfold const_seq_from.
    destruct (lt_dec 0 (k + 1)) as [O_lt_kplus1 | not_O_lt_kplus1].
    + assert (0 <= k) as O_le_k by lia.
      exact (H1 0 O_le_k).
    + exact (proj1 Hn_kplus1).
  - simpl; unfold const_seq_from.
    destruct (lt_dec (l + 1) (k + 1)) as [lplus1_lt_kplus1 | not_lplus1_lt_kplus1].
    + split.
      * assert (l + 1 <= k) as lplus1_le_k by lia.
        exact (H1 (l + 1) lplus1_le_k).
      * destruct (lt_dec l (k + 1)) as [l_lt_kplus1 | not_l_lt_kplus1].
        -- assert (S l <= k) as Sl_le_k by lia.
           exact (proj2 (H (S l) Sl_le_k)).
        -- assert False by lia; contradiction.
    + split.
      * exact (proj1 Hn_kplus1).
      * destruct (lt_dec l (k + 1)) as [l_lt_kplus1 | not_l_lt_kplus1].
        -- assert (l = k) as l_eq_k by lia.
           rewrite l_eq_k.
           exact (proj2 Hn_kplus1).
        -- assert False by lia; contradiction.
Qed.


Theorem full_rec_index_seq_with_prop {Q : nat -> Prop}
  (H0 : {n0 : nat | Q n0})
  (Hstep : forall (k : nat) (n : nat -> nat),
    (forall l : nat, l <= k -> Q (n l)) -> (forall l : nat, l < k -> n l < n (l + 1)) ->
    {n_kplus1 : nat | Q n_kplus1 /\ n k < n_kplus1})
  : {n : nat -> nat | is_index_seq n /\ forall k : nat, Q (n k)}.
Proof.
  enough {n : nat -> nat | forall k : nat, index_seq_prop_family Q k n} as [n Hn].
  { exists n.
    apply reformulate_final_prop_index.
    exact Hn.
  }
  destruct H0 as [n0 Hn0].
  apply (full_rec_seq_with_prop (dep_only_on_start_index_seq_prop_family Q) n0).
  - apply (reformulate_base_prop_index (const_seq n0)).
    exact Hn0.
  - intro k.
    assert (S k = k + 1) as Sk_eq_kplus1 by lia; rewrite Sk_eq_kplus1.
    apply reformulate_step_prop_index.
    apply Hstep.
Qed.


Definition dep_choice := non_dep_dep_functional_choice choice.
Check dep_choice.
Print DependentFunctionalChoice.
Print DependentFunctionalChoice_on.

Lemma help_with_choice {A B C : Type} {D E : A -> B -> Prop} {P : A -> B -> C -> Prop} :
  (forall (a : A) (b : B), D a b -> E a b-> exists c : C, P a b c) ->
  (exists f : forall (a : A) (b : B), D a b -> E a b -> C, forall (a : A) (b : B) (d : D a b) (e : E a b), P a b (f a b d e)).
Proof.
  intro H.
  apply (dep_choice _ _ (fun a f => forall (b : B) (d : D a b) (e : E a b), P a b (f b d e))).
  intro a.
  apply (dep_choice _ _ (fun b f => forall (d : D a b) (e : E a b), P a b (f d e))).
  intro b.
  apply (choice (fun d f => forall (e : E a b), P a b (f e))).
  intro d.
  apply (choice (fun e c => P a b c)).
  apply (H a b d).
Qed.

Theorem weak_full_rec_index_seq_with_prop {Q : nat -> Prop}
  (H0 : exists n0 : nat, Q n0)
  (Hstep : forall (k : nat) (n : nat -> nat),
    (forall l : nat, l <= k -> Q (n l)) -> (forall l : nat, l < k -> n l < n (l + 1)) ->
    exists n_kplus1 : nat, Q n_kplus1 /\ n k < n_kplus1)
  : exists n : nat -> nat, is_index_seq n /\ forall k : nat, Q (n k).
Proof.
  destruct H0 as [n0 Hn0].
  assert {n0 | Q n0} as H0sig by (exists n0; exact Hn0).
  (* Transform Hstep using choice such that the existence statement is at the start so it can be destructed. *)
  pose (help_with_choice Hstep) as Hstep2.
  destruct Hstep2 as [f Hf].
  (* Use strong version to prove existence statement. *)
  enough {n : nat -> nat | is_index_seq n /\ (forall k : nat, Q (n k))} as [n Hn].
  { exists n; exact Hn. }
  apply (full_rec_index_seq_with_prop H0sig).
  (* Use transformed Hstep to prove strong Hstep condition. *)
  intros k n H1 H2.
  exists (f k n H1 H2).
  apply Hf.
Qed.

End FullRecursiveIndexSequence.



Section Tactics.

From Ltac2 Require Import Ltac2.
From Ltac2 Require Import Message.


Require Export Waterproof.tactics.goal_wrappers.
Ltac2 Type exn ::= [ RecSeqError(string) ].
(*
(* 
Ltac2 concat (x1 : string) (x2 : string) : string := *)
  (* Taken from https://www.joachim-breitner.de/blog/777-Named_goals_in_Coq *)
  (* Horribly manual string manipulations. Does this mean I should
     go to the Ocaml level?
  *)
  let strcpy s1 s2 o :=
    let rec go := fun n =>
      match Int.lt n (String.length s2) with
      | true => String.set s1 (Int.add o n) (String.get s2 n); go (Int.add n 1)
      | false => ()
      end
    in go 0
  in
  let concat := fun s1 s2 =>
    let l := Int.add (Int.add (String.length s1) (String.length s2)) 1 in
    let s := String.make l (Char.of_int 95) in
    strcpy s s1 0;
    strcpy s s2 (Int.add (String.length s1) 1);
    s
  in
  concat x1 x2.

Ltac2 test (x : ident) :=
  match Ident.of_string (concat (Ident.to_string x) "kplus1") with
  | Some y => print (of_ident y); assert True as $y by auto
  | None => print (of_string "fail")
  end.

Goal (forall n : nat, False).
  intro n.
  test @n.
  clear n_kplus1.
*)

Ltac2 recursive_def_index_seq (m : ident) :=
  lazy_match! goal with
  | [ |- exists n : nat -> nat, is_index_seq n /\ forall k : nat, @?p n k ] => (*@?p*)
    lazy_match! p with
    | fun (n : nat -> nat) (k : nat) => ?q (n k) =>
      apply (@weak_full_rec_index_seq_with_prop $q);
      Control.focus 1 1 (fun () =>
      ()
      )

    | _ => Control.zero (RecSeqError "Cannot apply tactic.")
    end
  | [ |- _ ] => Control.zero (RecSeqError "Cannot apply tactic.")
  end.

Ltac2 Notation "Define" "the" "index" "sequence" n(ident) "recursively" := 
    panic_if_goal_wrapped ();
    recursive_def_index_seq n.

(* Test *)
Variable P : nat -> Prop.
Goal (exists n : nat -> nat, is_index_seq n /\ forall k : nat, P (n k)).
Proof.
  recursive_def_index_seq @m.
  - pose (m0 := 0); exists m0.
    admit.
  - 
    intros k m H1 H2.
    pose (m_kplus1 := 0); exists m_kplus1.
    split.
    + admit.
    + admit.




















