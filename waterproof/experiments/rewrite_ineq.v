From Ltac2 Require Import Ltac2.

Require Import Reals.
Require Import micromega.Lra.
Require Import Coq.Structures.Orders.
Require Import ROrderedType.
Require Import Waterproof.auxiliary.
Require Import Waterproof.tactics.forward_reasoning.rewrite_using.
Require Import Waterproof.tactics.forward_reasoning.forward_reasoning_aux.
Require Import Waterproof.waterprove.waterprove.
Require Import Waterproof.AllTactics.

Require Import Waterproof.load_database.RealsAndIntegers.

Require Import Waterproof.set_search_depth.To_3.

Section rewrite_inequalities.

Open Scope R_scope.
Import R_as_OT.

Inductive comp_rel :=
| comp_eq
| comp_lt
| comp_le
| comp_nil.

Definition comp_rel_to_rel (crel : comp_rel) : (t -> t -> Prop) :=
match crel with
| comp_eq => (fun x y => eq x y)
| comp_lt => (fun x y => lt x y)
| comp_le => (fun x y => le x y)
| comp_nil => (fun x y => True)
end.

Inductive ineq_chain :=
  | embed_t : t -> ineq_chain
  | chain_ineq : comp_rel -> ineq_chain -> ineq_chain -> ineq_chain.

Notation "x &<= y" := (chain_ineq comp_le x y) (at level 71, right associativity).
Notation "x &< y" := (chain_ineq comp_lt x y) (at level 71, right associativity).
Notation "x &= y" := (chain_ineq comp_eq x y) (at level 71, right associativity).

Definition embed_R (x : R) := embed_t x.
Coercion embed_R : R >-> ineq_chain.

Fixpoint ineq_to_head (ineq : ineq_chain) : t :=
match ineq with 
| embed_t x => x
| chain_ineq rel m l => ineq_to_head m
end.

Fixpoint ineq_to_tail (ineq : ineq_chain) : t :=
match ineq with 
| embed_t x => x
| chain_ineq rel m l => ineq_to_tail l
end.

Fixpoint ineq_to_prop_list (ineq : ineq_chain) : (list Prop).
induction ineq.
exact nil.
exact ((ineq_to_prop_list ineq1)++
      (((comp_rel_to_rel c) (ineq_to_tail ineq1) (ineq_to_head ineq2))::nil)
      ++(ineq_to_prop_list ineq2))%list.
Defined.

Fixpoint prop_list_and (prop_list : list Prop) : Prop.
induction prop_list.
exact True.
exact (and a (prop_list_and prop_list)).
Defined.

Definition ineq_to_prop (ineq : ineq_chain ):= 
  prop_list_and (ineq_to_prop_list ineq).

Coercion ineq_to_prop : ineq_chain >-> Sortclass.
Notation "& y" := (ineq_to_prop y) (at level 98).

Hint Extern 0 (ineq_to_prop _) => repeat split; simpl : reals. 
Hint Extern 0 (R_as_OT.lt _ _) => unfold R_as_OT.lt : reals.
Hint Extern 0 (R_as_OT.le _ _) => unfold R_as_OT.le : reals.

(* This may become relevant only later 

Fixpoint ineq_to_list (ineq : ineq_chain) : (list (comp_rel)).
induction ineq.
- exact nil.
- exact ((ineq_to_list ineq1)++(cons c nil)++(ineq_to_list ineq2))%list.
Defined.

Definition relation_flow (crel1: comp_rel) (crel2 : comp_rel) 
  : comp_rel :=
match crel1 with 
| comp_eq =>
  match crel2 with 
  | comp_eq => comp_eq
  | comp_lt => comp_lt
  | comp_le => comp_le
  | comp_nil => comp_eq
  end
| comp_lt =>
  match crel2 with
  | comp_eq => comp_lt
  | comp_lt => comp_lt
  | comp_le => comp_lt
  | comp_nil => comp_lt
  end
| comp_le =>
  match crel2 with
  | comp_eq => comp_le
  | comp_lt => comp_lt
  | comp_le => comp_le
  | comp_nil => comp_le
  end
| comp_nil => crel2
end.

Fixpoint find_global_comp_rel (rel_list : list comp_rel) : (comp_rel)
  :=
match rel_list with
| nil => comp_nil
| cons crel crel_list =>
  relation_flow (find_global_comp_rel crel_list)
                crel 
end.

Definition find_global_statement (ineq : ineq_chain): Prop :=
comp_rel_to_rel (find_global_comp_rel (ineq_to_list ineq)) (( ineq_to_head ineq)) (ineq_to_tail ineq).

Eval compute in (find_global_statement (
  (0 &= 2 &<= 1 + 1 &= 3))).

Eval compute in (my_ineq_to_prop (0 &= 2 &<= 1 + 1 &= 3)).

Lemma test : (my_ineq_to_prop (0 &< 2 &<= 1 + 1 &< 3)).
cbv.
repeat split; 
ltac1:(lra).


Ltac2 solve_chain_ineq (t : constr) :=
let w := Fresh.fresh (Fresh.Free.of_goal ()) @chain_statement_to_assert in
let glob_stat := Fresh.fresh (Fresh.Free.of_goal ()) @global_statement_to_assert in
assert ($w : my_ineq_to_prop $t);
Control.focus 1 1 (fun () =>
simpl;
repeat split;
Control.enter (fun () =>
waterprove_without_hint (Control.goal ()) constr:(dummy_lemma) false));
assert ($glob_stat : (find_global_statement $t)) 
  by (cbv; waterprove_without_hint constr:(find_global_statement $t) constr:(dummy_lemma) false).

(*; Message.print(Message.of_constr &u); Message.print (Message.of_constr 
  constr:(comp_rel_to_rel find_global_statement $s))).*)

Hint Extern 0 (and _ _) => (repeat split) : reals.

Hint Unfold ineq_to_head.

Notation "& y" := (my_ineq_to_prop y) (at level 98).
 
Definition force_to_prop (p : Prop) := p.

Ltac2 new_assert_and_prove_sublemma (id: ident) (conclusion: constr) 
                                (proving_lemma: constr option) :=
    let prop_concl := constr:($conclusion:Prop) in
    let help_lemma := unwrap_optional_lemma proving_lemma
    in
    let by_arg () := waterprove_without_hint prop_concl help_lemma true
    in
    let proof_attempt () := Aux.ltac2_assert_with_by id prop_concl by_arg
    in
    match Control.case proof_attempt with
    | Val _ => idtac () (*print (of_string ("New sublemma successfully added."))*)
    | Err exn => Control.zero exn
    end.

Require Import micromega.Lra.
Lemma test : (3 < 5).
(* new_assert_and_prove_sublemma ident:(asdf) constr:(3&<4) None.
It holds that asdf : (3 &< 4 : Prop).
    let prop_concl := constr:((3 &< 5):Prop) in
    let by_arg () := waterprove_without_hint prop_concl constr:(dummy_lemma) true
    in
    let proof_attempt () := Aux.ltac2_assert_with_by @bla prop_concl by_arg
    in
    match Control.case proof_attempt with
    | Val _ => idtac () (*print (of_string ("New sublemma successfully added."))*)
    | Err exn => Control.zero exn
    end. 

let s := constr:((3 &< 5) : Prop)
  in assert $s; trivial.
It holds that asdf : (3 &< 5).
assert (my_ineq_to_prop (3 &< 5 &< 7)) by (simpl; waterprove_without_hint constr:(3&<5) constr:(dummy_lemma)).
{
  simpl.
  
  repeat split. unfold comp_rel_to_rel. ltac1:(lra). *)
assert (& 3 &< 5).
simpl.
repeat split.
ltac1:(lra).
solve_chain_ineq constr:(3 &< 5).
It holds that asdf : (& 3 &< 5).
(*solve_chain_ineq constr:(3 &< 5). *)
Abort.

Ltac2 rewrite_ineq (t : constr) := 
  solve_chain_ineq t;
  assumption.

Ltac2 Notation "Rewrite" "(in)equality" ineq(constr) :=
  rewrite_ineq ineq.

Lemma test : (3 < 5).
Rewrite (in)equality (3 &< 5).
Qed.
(*  (* See if provided constr is of the right type *)
  (* Try to prove the provided constr *)
  (* Convert the goal *)
  if (Aux.check_constr_type_equal t constr:(embed_R 0))
  then
    (* See if provided constr is compatible with the goal *)
    lazy_match! goal with 
    | [|- Rlt ?s ?t] => 
      (* Check on which side the tactic should act *)
      Message.print(Message.of_string "blabla");
      (* Prove the statements *)
      solve_chain_ineq t
    | [|- _ ] => Control.throw (Control.zero (RewriteError "You cannot do this right now, 
   because the goal is not an (in)equality"))
    end
  else
    Control.throw (Control.zero (RewriteError
      "The argument you provided was not of the right type.")). *)

Lemma my_test : 0 < 1.
Proof.
rewrite_ineq constr:(0 &< 1/2 &< 1).
Qed.

Ltac2 Eval rewrite_ineq constr:(2 &< 3 &= 3).

Ltac2 Eval Message.print(Message.of_constr constr:(Aux.type_of (2 &< 3 &= 3))).

Ltac2 Eval Aux.check_constr_type_equal constr:(2 &< 3 &= 3) constr:(my_ineq).
  *)




