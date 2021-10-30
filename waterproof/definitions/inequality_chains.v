(** * [inequality_chains.v]
Authors:
  - Jim Portegies
  - Jelle Wemmenhove
Creation date: 17 June 2021

A module to write and use chains of inequalities such as 
  (& 3 &<= 4 &< 7 &= 3 + 4 &< 8 )

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

Require Import Reals.
(** We make use of the module OrderedTypeFull to 
    be able to generalize easily to other types. After the following imports, 
    t denotes the ordered type. *)
Require Import Coq.Structures.Orders.
Require Import ROrderedType.

Open Scope R_scope.
Import R_as_OT.

(** ** comp_rel
An inductive type that records which comparison relation to use.
*)
Inductive comp_rel :=
| comp_eq
| comp_lt
| comp_le.

(** ** comp_rel_to_rel
Get the corresponding relation from a comp_rel record.

    Arguments:
        - [crel : comp_rel] The comp_rel record of the relation

    Returns:
        - [t -> t -> Prop] The corresponding relation. 
*)
Definition comp_rel_to_rel (crel : comp_rel) : (t -> t -> Prop) :=
match crel with
| comp_eq => (fun x y => eq x y)
| comp_lt => (fun x y => lt x y)
| comp_le => (fun x y => le x y)
end.

(** ** ineq_chain
The actual (in)equality chain. This object is defined inductively, with 
the base case corresponding to just a term in t.
*)
Inductive ineq_chain :=
  | embed_t : t -> ineq_chain
  | chain_ineq : comp_rel -> ineq_chain -> ineq_chain -> ineq_chain.

(** ** embeddings
Create embeddings of datatypes into (in)equality chains
*)
Definition embed_R (x : R) := embed_t x.
Coercion embed_R : R >-> ineq_chain.

(** ** ineq_to_head
Get the first term in an (in)equality chain
    Arguments:
        - [ineq : ineq_chain] the (in)equality chain

    Returns:
        - [t] the first term of the (in)equality chain
*)
Fixpoint ineq_to_head (ineq : ineq_chain) : t :=
match ineq with 
| embed_t x => x
| chain_ineq rel m l => ineq_to_head m
end.

(** ** ineq_to_tail
Get the last term in an (in)equality chain
    Arguments:
        - [ineq : ineq_chain] the (in)equality chain

    Returns:
        - [t] the last term of the (in)equality chain
*)
Fixpoint ineq_to_tail (ineq : ineq_chain) : t :=
match ineq with 
| embed_t x => x
| chain_ineq rel m l => ineq_to_tail l
end.

(** ** ineq_to_prop_list
Get the list of the propositions contained in an (in)equality chain.
For instance, ineq_to_prop_list (& 3 <& 5 &= 2 + 3) should give a list containing
(3 < 5) and (5 = 2+3).

    Arguments:
        - [ineq : ineq_chain] the (in)equality chain to convert to a list of propositions

    Returns:
        - [list Prop] a list of the propositions contained in an (in)equality chain.
*)
Fixpoint ineq_to_prop_list (ineq : ineq_chain) : (list Prop).
induction ineq.
exact nil.
exact ((ineq_to_prop_list ineq1)++
      (((comp_rel_to_rel c) (ineq_to_tail ineq1) (ineq_to_head ineq2))::nil)
      ++(ineq_to_prop_list ineq2))%list.
Defined.

(** ** prop_list_and
Combine the propositions in a prop list to a big 'and' statement.
A list containing (3 < 5) and (5 = 2 + 3) gets converted to
    (3 < 5) /\ (5 = 2 + 3).
TODO: should we use a standard library function instead?
*)
Fixpoint prop_list_and (prop_list : list Prop) : Prop.
induction prop_list.
exact True.
exact (and a (prop_list_and prop_list)).
Defined.

(** ** ineq_to_prop
Get the proposition corresponding to a chain of (in)equalities. These are 
all (in)equalities contained in the (in)equality chain combined in a big 'and' statement.

    Arguments:
        [ineq : ineq_chain] The (in)equality chain to convert to a proposition

    Returns:
        [Prop] the proposition corresponding to the (in)equality chain 
*)
Definition ineq_to_prop (ineq : ineq_chain ) : Prop := 
  prop_list_and (ineq_to_prop_list ineq).

(** Coerce (in)equality chains to propositions if necessary *)
Coercion ineq_to_prop : ineq_chain >-> Sortclass.

Notation "x &<= y" := (chain_ineq comp_le x y) (at level 71, right associativity).
Notation "x &< y" := (chain_ineq comp_lt x y) (at level 71, right associativity).
Notation "x &= y" := (chain_ineq comp_eq x y) (at level 71, right associativity).
Notation "& y" := (ineq_to_prop y) (at level 98).