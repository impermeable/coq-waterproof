(** We make use of the module OrderedTypeFull to 
    be able to generalize easily to other types. After the following imports, 
    t denotes the ordered type. *)
Require Import Coq.Structures.Orders.

(** ** comp_rel
An inductive type that records which comparison relation to use.
*)
Inductive comp_rel :=
| comp_eq
| comp_lt
| comp_le.

Module Type INEQUALITY_CHAINS.
Declare Module M : OrderedTypeFull.

(*Parameter comp_rel_to_pred : comp_rel -> M.t -> M.t -> Prop.*)
Parameter ineq_chain : Type.
Parameter embed : M.t -> ineq_chain.
Parameter link : ineq_chain -> comp_rel -> M.t -> ineq_chain.
Parameter find_global_statement : ineq_chain -> Prop.
Parameter ineq_to_prop : ineq_chain -> Prop.

End INEQUALITY_CHAINS.

Module ChainImplementations (M : OrderedTypeFull) <: INEQUALITY_CHAINS with Module M := M.
Module M := M.
Import M.

(** ** comp_rel_to_rel
Get the corresponding relation from a comp_rel record.

    Arguments:
        - [crel : comp_rel] The comp_rel record of the relation

    Returns:
        - [t -> t -> Prop] The corresponding relation. 
*)
Definition comp_rel_to_pred (crel : comp_rel) : (t -> t -> Prop) :=
match crel with
| comp_eq => (fun x y => eq x y)
| comp_lt => (fun x y => lt x y)
| comp_le => (fun x y => le x y)
end.

(** ** ineq_chain
The actual (in)equality chain. This object is defined inductively, with 
the base case corresponding to just a term in t.
*)
Inductive my_ineq_chain :=
  | my_embed : t -> my_ineq_chain (* iterpret as chain 't = t' *)
  | my_link : my_ineq_chain -> comp_rel -> t -> my_ineq_chain.

Definition ineq_chain := my_ineq_chain.
Definition embed := my_embed.
Definition link := my_link.

(** ** ineq_to_head
Get the first term in an (in)equality chain
    Arguments:
        - [ineq : ineq_chain] the (in)equality chain

    Returns:
        - [t] the first term of the (in)equality chain
*)
Fixpoint ineq_to_head (chain : my_ineq_chain) : t :=
match chain with 
| my_embed x => x
| my_link chain rel z => ineq_to_head chain
end.

(** ** ineq_to_tail
Get the last term in an (in)equality chain
    Arguments:
        - [ineq : ineq_chain] the (in)equality chain

    Returns:
        - [t] the last term of the (in)equality chain
*)
Definition ineq_to_tail (chain : my_ineq_chain) : t :=
match chain with 
| my_embed x => x
| my_link chain rel z => z
end.

(** 
Helper function for the algorithm that determines the global relation in 
an (in)equality chain.

    Arguments:
        - [crel1 : comp_rel] the comparison relation on the left
        - [crel2 : comp_rel] the comparison relation on the right

    Returns:
        - [comp_rel] the comparison relation that you get when combining the two
*)
Definition relation_flow (crel1: comp_rel) (crel2 : comp_rel) 
  : comp_rel :=
match crel1 with 
| comp_eq => crel2
| comp_lt => comp_lt
| comp_le =>
  match crel2 with
  | comp_eq => comp_le
  | comp_lt => comp_lt
  | comp_le => comp_le
  end
end.

(**
Find the global relation from a list of comparison relations.

    Arguments:
        - [rel_list : list comp_rel] the list of comparison relations

    Returns:
        - [comp_rel] the encoding of the comparison relation
*)
Fixpoint find_global_comp_rel (chain : my_ineq_chain) : (comp_rel) :=
match chain with
| my_embed x => comp_eq
| my_link chain rel z => relation_flow (find_global_comp_rel chain) rel
end.

(** ** find_global_statement
Find the corresponding global statement from an (in)equality chain.
For instance, find_global_statement (3 &< 5 &= 5 &<= 8) should give (3 < 8).

    Arguments:
        - [ineq : ineq_chain] the (in)equality chain

    Returns:
        - [Prop] the global statement
*)
Definition find_global_statement (chain : my_ineq_chain): Prop :=
comp_rel_to_pred (find_global_comp_rel chain) (ineq_to_head chain) (ineq_to_tail chain).


(** ** ineq_to_prop
Get the proposition corresponding to a chain of (in)equalities. These are 
all (in)equalities contained in the (in)equality chain combined in a big 'and' statement.

    Arguments:
        [ineq : ineq_chain] The (in)equality chain to convert to a proposition

    Returns:
        [Prop] the proposition corresponding to the (in)equality chain 
*)
Fixpoint ineq_to_prop (chain : my_ineq_chain) : Prop := 
match chain with
| my_embed x => (x = x)
| my_link chain rel z => (ineq_to_prop chain) /\ (comp_rel_to_pred rel (ineq_to_tail chain) z)
end.

End ChainImplementations.



Require Import Reals.
Require Import ROrderedType.
Open Scope R_scope.
Import R_as_OT.

Module ineq_chain_R := ChainImplementations(R_as_OT).
Module ineq_chain_nat := ChainImplementations(Nat).


(** ** embeddings
Create embeddings of datatypes into (in)equality chains
*)
Coercion ineq_chain_R.embed : R >-> ineq_chain_R.my_ineq_chain.
Coercion ineq_chain_nat.embed : nat >-> ineq_chain_nat.my_ineq_chain.


Notation "c &<= y" := (ineq_chain_R.link c comp_le y) (at level 71, left associativity) : R_scope.
Notation "c &≤ y" := (ineq_chain_R.link c comp_le y) (at level 71, left associativity) : R_scope.
Notation "c &< y" := (ineq_chain_R.link c comp_lt y) (at level 71, left associativity) : R_scope.
Notation "c &= y" := (ineq_chain_R.link c comp_eq y) (at level 71, left associativity) : R_scope.
Notation "& c" := (ineq_chain_R.ineq_to_prop c) (at level 98) : R_scope.

Notation "c &<= y" := (ineq_chain_nat.link c comp_le y) (at level 71, left associativity) : nat_scope.
Notation "c &≤ y" := (ineq_chain_nat.link c comp_le y) (at level 71, left associativity) : nat_scope.
Notation "c &< y" := (ineq_chain_nat.link c comp_lt y) (at level 71, left associativity) : nat_scope.
Notation "c &= y" := (ineq_chain_nat.link c comp_eq y) (at level 71, left associativity) : nat_scope.
Notation "& c" := (ineq_chain_nat.ineq_to_prop c) (at level 98) : nat_scope.

