(** * [inequality_chains.v]
Authors:
  - Jim Portegies
  - Jelle Wemmenhove
Creation date: 17 June 2021

A module to write and use chains of inequalities such as 
  (& 3 &<= 4 &< 7 &= 3 + 4 &< 8)  or
  (& 8 &> 3 + 4 &= 7 &> 4 &>= 3).
The combination of <- and > symbols in the same chain is syntactically valid, 
but the kernel does not know how their combination should be interpreted.
When used in a proof, this results in an error that informs the user about the missing interpretation,
the error can be hard to understand without knowle3dge of the underlying implementation.

We use type classes to overload the chain link symbols like '&=' and '&<'.

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

(* Abstract representations for =, <, ≤, > and ≥ symbols.*)
Inductive EqualRel := | chain_eq.
Inductive LessRel := | chain_lt | chain_le.
Inductive GreaterRel := | chain_gt | chain_ge.

(* Types of chains. *)
(* Only contains =-relations. *)
Inductive EqualChain (T : Type) :=
| base_ec : T -> EqualRel * T -> EqualChain T
| link_ec_eq : EqualChain T -> EqualRel * T -> EqualChain T.
Inductive LessChain (T : Type) :=
| base_lc : T -> LessRel * T -> LessChain T
| link_ec_less : EqualChain T -> LessRel  * T -> LessChain T  (* link < or ≤ and term to equality chain *)
| link_lc_eq   : LessChain T  -> EqualRel * T -> LessChain T  (* link term to chain with =-relation*)
| link_lc_less : LessChain T  -> LessRel  * T -> LessChain T. (* link term to chain with <- or ≤-relation*)
Inductive GreaterChain (T : Type) :=
| base_gc : T -> GreaterRel * T -> GreaterChain T
| link_ec_grtr : EqualChain T   -> GreaterRel * T -> GreaterChain T (* link > or ≥ and term to equality chain *)
| link_gc_eq   : GreaterChain T -> EqualRel   * T -> GreaterChain T (* link term to chain with =-relation*)
| link_gc_grtr : GreaterChain T -> GreaterRel * T -> GreaterChain T. (* link term to chain with >- or ≥-relation*)

(* Type classes for linking new terms to chains.
   Type classes are used for notation overloading of link function 'chain_link' *)
Class ChainLink (A B C : Type) := chain_link : A -> B -> C.
#[export] Instance link_ec_eq_inst   (T : Type) : ChainLink (EqualChain T) (EqualRel * T) (EqualChain T) := link_ec_eq T.
#[export] Instance link_ec_less_inst (T : Type) : ChainLink (EqualChain T) (LessRel  * T) (LessChain T) := link_ec_less T.
#[export] Instance link_lc_eq_inst   (T : Type) : ChainLink (LessChain  T) (EqualRel * T) (LessChain T) := link_lc_eq T.
#[export] Instance link_lc_less_inst (T : Type) : ChainLink (LessChain  T) (LessRel  * T) (LessChain T) := link_lc_less T.
#[export] Instance link_ec_grtr_inst (T : Type) : ChainLink (EqualChain   T) (GreaterRel * T) (GreaterChain T) := link_ec_grtr T.
#[export] Instance link_gc_eq_inst   (T : Type) : ChainLink (GreaterChain T) (EqualRel   * T) (GreaterChain T) := link_gc_eq T.
#[export] Instance link_gc_grtr_inst (T : Type) : ChainLink (GreaterChain T) (GreaterRel * T) (GreaterChain T) := link_gc_grtr T.
Class ChainBase (A B C : Type) := chain_base : A -> B -> C.
#[export] Instance base_ec_inst (T : Type) : ChainBase T (EqualRel   * T) (EqualChain   T) := base_ec T.
#[export] Instance base_lc_inst (T : Type) : ChainBase T (LessRel    * T) (LessChain    T) := base_lc T.
#[export] Instance base_gc_inst (T : Type) : ChainBase T (GreaterRel * T) (GreaterChain T) := base_gc T.




(*
(* Type classes for linking new terms to chains.
   Type classes are used for notation overloading of link symbols like '&=' *)
Class EqLink (A B C: Type) := eq_link : A -> B -> C. (*notation: _ &= _ *)
#[export] Instance eq_base (T : Type) : EqLink T T (EqualChain T) := ec_base T.
#[export] Instance ec_eq_link (T : Type) : EqLink (EqualChain T) T (EqualChain T) := ec_link T.
#[export] Instance lc_eq_link (T : Type) : EqLink (LessChain T) T (LessChain T) := lc_link2 T.
#[export] Instance gc_eq_link (T : Type) : EqLink (GreaterChain T) T (GreaterChain T) := gc_link2 T.

Class LtLink (A B C : Type) := lt_link : A -> B -> C. (*notation: _ &< _ *)
#[export] Instance lt_base (T : Type) : LtLink  T T (LessChain T) := 
  fun x => lc_base T x rel_lt.
#[export] Instance ec_lt_link (T : Type) : LtLink (EqualChain T) T (LessChain T) :=
  fun c1 => lc_link1 T c1 rel_lt.
#[export] Instance lc_lt_link (T : Type) : LtLink (LessChain T) T (LessChain T) := 
  fun c1 => lc_link3 T c1 rel_lt.

Class LeLink (A B C : Type) := le_link : A -> B -> C. (*notation: _ &≤ _ *)
#[export] Instance le_base (T : Type) : LeLink T T (LessChain T) := 
  fun x => lc_base T x rel_le.
#[export] Instance ec_le_link (T : Type) : LeLink (EqualChain T) T (LessChain T) := 
  fun c1 => lc_link1 T c1 rel_le.
#[export] Instance lc_le_link (T : Type) : LeLink (LessChain T) T (LessChain T) := 
  fun c1 => lc_link3 T c1 rel_le.

Class GtLink (A B C : Type) := gt_link : A -> B -> C. (*notation: _ &> _ *)
#[export] Instance gt_base (T : Type) : GtLink  T T (GreaterChain T) := 
  fun x => gc_base T x rel_gt.
#[export] Instance ec_gt_link (T : Type) : GtLink (EqualChain T) T (GreaterChain T) :=
  fun c1 => gc_link1 T c1 rel_gt.
#[export] Instance gc_gt_link (T : Type) : GtLink (GreaterChain T) T (GreaterChain T) := 
  fun c1 => gc_link3 T c1 rel_gt.

Class GeLink (A B C : Type) := ge_link : A -> B -> C. (*notation: _ &≥ _ *)
#[export] Instance ge_base (T : Type) : GeLink T T (GreaterChain T) := 
  fun x => gc_base T x rel_ge.
#[export] Instance ec_ge_link (T : Type) : GeLink (EqualChain T) T (GreaterChain T) := 
  fun c1 => gc_link1 T c1 rel_ge.
#[export] Instance gc_ge_link (T : Type) : GeLink (GreaterChain T) T (GreaterChain T) := 
  fun c1 => gc_link3 T c1 rel_ge.
*)




(** Helper functions *)

(* Head: first term in a chain *)
Fixpoint ec_head {T : Type} (c : EqualChain T) : T :=
match c with
| base_ec _ x y => x
| link_ec_eq _ ec z => ec_head ec
end.
Fixpoint lc_head {T : Type} (c : LessChain T) : T :=
match c with
| base_lc _ x _       => x
| link_ec_less _ ec _ => ec_head ec
| link_lc_eq _ lc _   => lc_head lc
| link_lc_less _ lc _ => lc_head lc
end.
Fixpoint gc_head {T : Type} (c : GreaterChain T) : T :=
match c with
| base_gc _ x _       => x
| link_ec_grtr _ ec _ => ec_head ec
| link_gc_eq _ gc _   => gc_head gc
| link_gc_grtr _ gc _ => gc_head gc
end.

(* Tail: last term in a chain *)
Definition ec_tail {T : Type} (c : EqualChain T) : T :=
match c with
| base_ec _ _ (_,y)    => y
| link_ec_eq _ _ (_,z) => z
end.
Definition lc_tail {T : Type} (c : LessChain T) : T :=
match c with
| base_lc _ _ (_,y)      => y
| link_ec_less _ _ (_,z) => z
| link_lc_eq _ _ (_,z)   => z
| link_lc_less _ _ (_,z) => z
end.
Definition gc_tail {T : Type} (c : GreaterChain T) : T :=
match c with
| base_gc _ x (_,y)      => y
| link_ec_grtr _ _ (_,z) => z
| link_gc_eq _ _ (_,z)   => z
| link_gc_grtr _ _ (_,z) => z
end.


(* Chains contain multiple meanings:
    the global statement of (0 < 1 <= 2) is (0 < 2),
    the weak global statement            is (0 <= 2),
    the total statement                  is (0 < 1 /\ 1 <= 2)

   Again a type class is used such that we can use the same terms and notations
    for all three types of chains. *)
Class InterpretableChain (T : Type) (C : Type -> Type) := 
  { global_statement : C T -> Prop
  ; weak_global_statement : C T -> Prop
  ; total_statement : C T -> Prop
  }.

(* Notations for link type classes *)
Declare Scope chain_scope.
Delimit Scope chain_scope with chain.
Notation "< y" :=  (chain_lt, y) (at level 69, y at next level) : chain_scope.
Notation "<= y" := (chain_le, y) (at level 69, y at next level) : chain_scope.
Notation "≤ y" :=  (chain_le, y) (at level 69, y at next level) : chain_scope.
Notation "= y" :=  (chain_eq, y) (at level 69, y at next level) : chain_scope.
Notation "> y" :=  (chain_gt, y) (at level 69, y at next level) : chain_scope.
Notation ">= y" := (chain_ge, y) (at level 69, y at next level) : chain_scope.
Notation "≥ y" :=  (chain_ge, y) (at level 69, y at next level) : chain_scope.
(* Full chain *)
Notation "& x ly lz .. lw" := (total_statement (chain_link .. (chain_link (chain_base x ly%chain) lz%chain) .. lw%chain))
  (at level 70, x at next level, ly at next level, lw at next level).

(** Global & total statement - EqualChain *)
Definition ec_global_statement (T : Type) (c : EqualChain T) : Prop :=
  ec_head c = ec_tail c.
Fixpoint ec_total_statement (T : Type) (c : EqualChain T) : Prop :=
match c with
| base_ec _ x (_,y)     => (x = y)
| link_ec_eq _ ec (_,z) => (ec_total_statement _ ec) /\ (ec_tail ec = z)
end.
#[export] Instance ec_interpretable (T : Type) : InterpretableChain T EqualChain :=
  { global_statement := ec_global_statement T
  ; weak_global_statement := ec_global_statement T
  ; total_statement := ec_total_statement T
  }.

(** Helper functions specific to Less- and GreaterChain. *)
(* The global relation resulting from a combination of relations [rel1] and [rel2]. *)
Definition less_relation_flow (rel1 rel2 : LessRel) : LessRel :=
match rel1 with
| chain_lt => chain_lt
| chain_le => rel2
end.
Definition grtr_relation_flow (rel1 rel2 : GreaterRel) : GreaterRel :=
match rel1 with
| chain_gt => chain_gt
| chain_ge => rel2
end.
(* Returns the global relation of a LessChain. *)
Fixpoint global_less_rel {T : Type} (c : LessChain T) : LessRel :=
match c with
| base_lc _ _ (rel,_)       => rel
| link_ec_less _ _ (rel,_)  => rel
| link_lc_eq _ lc _         => global_less_rel lc
| link_lc_less _ lc (rel,_) => less_relation_flow (global_less_rel lc) rel
end.
(* Returns the global relation of a GreaterChain. *)
Fixpoint global_grtr_rel {T : Type} (c : GreaterChain T) : GreaterRel :=
match c with
| base_gc _ _ (rel,_)       => rel
| link_ec_grtr _ _ (rel,_)  => rel
| link_gc_eq _ gc _         => global_grtr_rel gc
| link_gc_grtr _ gc (rel,_) => grtr_relation_flow (global_grtr_rel gc) rel
end.

(* Functions to turn the abstract [LessRel] and [GreaterRel] relations into their concrete interpretations.
   We again use type classes to be able to use the same name for these functions across types that implement them.
  *)
Class OrderInterpretation (T : Type) := 
  { less_rel_to_pred : LessRel -> T -> T -> Prop
  ; grtr_rel_to_pred : GreaterRel -> T -> T -> Prop
  }.

(** Global & total statement - LessChain *)
Definition lc_global_statement (T : Type) `{! OrderInterpretation T} (c : LessChain T) : Prop :=
  less_rel_to_pred (global_less_rel c) (lc_head c) (lc_tail c).
Definition lc_weak_global_statement (T : Type) `{! OrderInterpretation T} (c : LessChain T) : Prop :=
  less_rel_to_pred chain_le (lc_head c) (lc_tail c).
Fixpoint lc_total_statement (T : Type) `{! OrderInterpretation T} (c : LessChain T) : Prop :=
match c with
| base_lc _ x (rel,y) => less_rel_to_pred rel x y
| link_ec_less _ ec (rel,z) => (ec_total_statement _ ec) /\ less_rel_to_pred rel (ec_tail ec) z
| link_lc_eq _ lc (_,z)     => (lc_total_statement _ lc) /\ (lc_tail lc = z)
| link_lc_less _ lc (rel,z) => (lc_total_statement _ lc) /\ less_rel_to_pred rel (lc_tail lc) z
end.
#[export] Instance lc_interpretable (T : Type) `{! OrderInterpretation T} : InterpretableChain T LessChain :=
  { global_statement := lc_global_statement T
  ; weak_global_statement := lc_weak_global_statement T
  ; total_statement := lc_total_statement T
  }.

(** Global & total statement - GreaterChain *)
Definition gc_global_statement (T : Type) `{! OrderInterpretation T} (c : GreaterChain T) : Prop :=
  grtr_rel_to_pred (global_grtr_rel c) (gc_head c) (gc_tail c).
Definition gc_weak_global_statement (T : Type) `{! OrderInterpretation T} (c : GreaterChain T) : Prop :=
  grtr_rel_to_pred chain_ge (gc_head c) (gc_tail c).
Fixpoint gc_total_statement (T : Type) `{! OrderInterpretation T} (c : GreaterChain T) : Prop :=
match c with
| base_gc _ x (rel,y) => grtr_rel_to_pred rel x y
| link_ec_grtr _ ec (rel,z) => (ec_total_statement _ ec) /\ grtr_rel_to_pred rel (ec_tail ec) z
| link_gc_eq _ gc (_,z) => (gc_total_statement _ gc) /\ (gc_tail gc = z)
| link_gc_grtr _ gc (rel,z) => (gc_total_statement _ gc) /\ grtr_rel_to_pred rel (gc_tail gc) z
end.
#[export] Instance gc_interpretable (T : Type) `{! OrderInterpretation T} : InterpretableChain T GreaterChain :=
  { global_statement := gc_global_statement T
  ; weak_global_statement := gc_weak_global_statement T
  ; total_statement := gc_total_statement T
  }.


(* Interpretations of [LessRel] and [GreaterRel] for the naturals. *)
#[export] Instance order_interpretation_nat : OrderInterpretation nat := 
  { less_rel_to_pred rel x y := match rel with | chain_lt => (x < y) | chain_le => (x <= y) end
  ; grtr_rel_to_pred rel x y := match rel with | chain_gt => (x > y) | chain_ge => (x >= y) end
  }.

(* Interpretations of [LessRel] and [GreaterRel] for the reals. *)
Require Import Reals.
Open Scope R_scope.
#[export] Instance order_interpretation_R : OrderInterpretation R := 
  { less_rel_to_pred rel x y := match rel with | chain_lt => (x < y) | chain_le => (x <= y) end
  ; grtr_rel_to_pred rel x y := match rel with | chain_gt => (x > y) | chain_ge => (x >= y) end
  }.
Close Scope R_scope.

(*
(* tests *)
Check (& 0 < 1 = 2 - 1 < 2).
Goal (& 0 < 1 = 2 - 1 < 2).
Proof. unfold total_statement; cbv.
Abort.
Check (& 0 < 1 = 2 - 1 > 1). (* No typeclass inference found. *)

Check (& INR 0 < 1 = 1). (* No typeclass inference found. *)
*)

(* Because the typeclasses used for the link-symbols '&=' are so general,
   they are unable to automatically make use of coercions,
   e.g. the chain (& INR 0 < 1 = 1) is not accepted, Coq says it is unable to find
   an interpretation for (EqLink R nat ?C).

   We thus have to add all these cases manually.
*)

(* Helper functions: functorality of chain types. *)
Fixpoint ec_map {A B : Type} (f : A -> B) (c : EqualChain A) : EqualChain B :=
match c with 
| base_ec _ x (rel,y)     => base_ec _ (f x) (rel,f y)
| link_ec_eq _ ec (rel,z) => link_ec_eq _ (ec_map f ec) (rel, f z)
end.
Fixpoint lc_map {A B : Type} (f : A -> B) (c : LessChain A) : LessChain B :=
match c with
| base_lc _ x (rel,y) => base_lc _ (f x) (rel, f y)
| link_ec_less _ ec (rel,z) => link_ec_less _ (ec_map f ec) (rel, f z)
| link_lc_eq _ lc (rel,z)   => link_lc_eq _ (lc_map f lc) (rel, f z)
| link_lc_less _ lc (rel,z) => link_lc_less _ (lc_map f lc) (rel, f z)
end.
Fixpoint gc_map {A B : Type} (f : A -> B) (c : GreaterChain A) : GreaterChain B :=
match c with
| base_gc _ x (rel,y) => base_gc _ (f x) (rel, f y)
| link_ec_grtr _ ec (rel,z) => link_ec_grtr _ (ec_map f ec) (rel, f z)
| link_gc_eq _ gc (rel,z)   => link_gc_eq _ (gc_map f gc) (rel, f z)
| link_gc_grtr _ gc (rel,z) => link_gc_grtr _ (gc_map f gc) (rel, f z)
end.

Definition snd_map {A B C : Type} (f : B -> C) (z : A * B) : A * C := (fst z, f (snd z)). 

(* embedding INR : nat -> R *)
(* EqualChain *)
#[export] Instance base_ec_nat_R : ChainBase nat (EqualRel * R) (EqualChain R) := fun n lx => base_ec R (INR n) lx.
#[export] Instance base_ec_R_nat : ChainBase R (EqualRel * nat) (EqualChain R) := fun x ln => base_ec R x (snd_map INR ln).
#[export] Instance link_ec_eq_nat_R : ChainLink (EqualChain nat) (EqualRel * R) (EqualChain R) := 
  fun ecn lx => link_ec_eq R (ec_map INR ecn) lx.
#[export] Instance link_ec_eq_R_nat : ChainLink (EqualChain R) (EqualRel * nat) (EqualChain R) := 
  fun ecx ln => link_ec_eq R ecx (snd_map INR ln).
(* LessChain *)
#[export] Instance base_lc_nat_R : ChainBase nat (LessRel * R) (LessChain R) := fun n lx => base_lc R (INR n) lx.
#[export] Instance base_lc_R_nat : ChainBase R (LessRel * nat) (LessChain R) := fun x ln => base_lc R x (snd_map INR ln).
#[export] Instance link_ec_less_nat_R : ChainLink (EqualChain nat) (LessRel * R) (LessChain R) :=
  fun ecn lx => link_ec_less R (ec_map INR ecn) lx.
#[export] Instance link_ec_less_R_nat : ChainLink (EqualChain R) (LessRel * nat) (LessChain R) :=
  fun ecx ln => link_ec_less R ecx (snd_map INR ln).
#[export] Instance link_lc_eq_nat_R : ChainLink (LessChain nat) (EqualRel * R) (LessChain R) := 
  fun lcn x => link_lc_eq R (lc_map INR lcn) x.
#[export] Instance link_lc_eq_R_nat : ChainLink (LessChain R) (EqualRel * nat) (LessChain R) := 
  fun lcx ln => link_lc_eq R lcx (snd_map INR ln).
#[export] Instance link_lc_less_nat_R : ChainLink (LessChain nat) (LessRel * R) (LessChain R) := 
  fun lcn lx => link_lc_less R (lc_map INR lcn) lx.
#[export] Instance link_lc_less_R_nat : ChainLink (LessChain R) (LessRel * nat) (LessChain R) := 
  fun lcx ln => link_lc_less R lcx (snd_map INR ln).
(* GreaterChain *)
#[export] Instance base_gc_nat_R : ChainBase nat (GreaterRel * R) (GreaterChain R) := fun n lx => base_gc R (INR n) lx.
#[export] Instance base_gc_R_nat : ChainBase R (GreaterRel * nat) (GreaterChain R) := fun x ln => base_gc R x (snd_map INR ln).
#[export] Instance link_ec_grtr_nat_R : ChainLink (EqualChain nat) (GreaterRel * R) (GreaterChain R) :=
  fun ecn lx => link_ec_grtr R (ec_map INR ecn) lx.
#[export] Instance link_ec_grtr_R_nat : ChainLink (EqualChain R) (GreaterRel * nat) (GreaterChain R) :=
  fun ecx ln => link_ec_grtr R ecx (snd_map INR ln).
#[export] Instance link_gc_eq_nat_R : ChainLink (GreaterChain nat) (EqualRel * R) (GreaterChain R) := 
  fun gcn x => link_gc_eq R (gc_map INR gcn) x.
#[export] Instance link_gc_eq_R_nat : ChainLink (GreaterChain R) (EqualRel * nat) (GreaterChain R) := 
  fun gcx ln => link_gc_eq R gcx (snd_map INR ln).
#[export] Instance link_gc_grtr_nat_R : ChainLink (GreaterChain nat) (GreaterRel * R) (GreaterChain R) := 
  fun gcn lx => link_gc_grtr R (gc_map INR gcn) lx.
#[export] Instance link_gc_grtr_R_nat : ChainLink (GreaterChain R) (GreaterRel * nat) (GreaterChain R) := 
  fun gcx ln => link_gc_grtr R gcx (snd_map INR ln).

(*
(* test *)
Check (& INR 0 < 1 = 1).
*)

(* embedding IZR : Z -> R *)
(* EqualChain *)
#[export] Instance base_ec_Z_R : ChainBase Z (EqualRel * R) (EqualChain R) := fun n lx => base_ec R (IZR n) lx.
#[export] Instance base_ec_R_Z : ChainBase R (EqualRel * Z) (EqualChain R) := fun x ln => base_ec R x (snd_map IZR ln).
#[export] Instance link_ec_eq_Z_R : ChainLink (EqualChain Z) (EqualRel * R) (EqualChain R) := 
  fun ecn lx => link_ec_eq R (ec_map IZR ecn) lx.
#[export] Instance link_ec_eq_R_Z : ChainLink (EqualChain R) (EqualRel * Z) (EqualChain R) := 
  fun ecx ln => link_ec_eq R ecx (snd_map IZR ln).
(* LessChain *)
#[export] Instance base_lc_Z_R : ChainBase Z (LessRel * R) (LessChain R) := fun n lx => base_lc R (IZR n) lx.
#[export] Instance base_lc_R_Z : ChainBase R (LessRel * Z) (LessChain R) := fun x ln => base_lc R x (snd_map IZR ln).
#[export] Instance link_ec_less_Z_R : ChainLink (EqualChain Z) (LessRel * R) (LessChain R) :=
  fun ecn lx => link_ec_less R (ec_map IZR ecn) lx.
#[export] Instance link_ec_less_R_Z : ChainLink (EqualChain R) (LessRel * Z) (LessChain R) :=
  fun ecx ln => link_ec_less R ecx (snd_map IZR ln).
#[export] Instance link_lc_eq_Z_R : ChainLink (LessChain Z) (EqualRel * R) (LessChain R) := 
  fun lcn x => link_lc_eq R (lc_map IZR lcn) x.
#[export] Instance link_lc_eq_R_Z : ChainLink (LessChain R) (EqualRel * Z) (LessChain R) := 
  fun lcx ln => link_lc_eq R lcx (snd_map IZR ln).
#[export] Instance link_lc_less_Z_R : ChainLink (LessChain Z) (LessRel * R) (LessChain R) := 
  fun lcn lx => link_lc_less R (lc_map IZR lcn) lx.
#[export] Instance link_lc_less_R_Z : ChainLink (LessChain R) (LessRel * Z) (LessChain R) := 
  fun lcx ln => link_lc_less R lcx (snd_map IZR ln).
(* GreaterChain *)
#[export] Instance base_gc_Z_R : ChainBase Z (GreaterRel * R) (GreaterChain R) := fun n lx => base_gc R (IZR n) lx.
#[export] Instance base_gc_R_Z : ChainBase R (GreaterRel * Z) (GreaterChain R) := fun x ln => base_gc R x (snd_map IZR ln).
#[export] Instance link_ec_grtr_Z_R : ChainLink (EqualChain Z) (GreaterRel * R) (GreaterChain R) :=
  fun ecn lx => link_ec_grtr R (ec_map IZR ecn) lx.
#[export] Instance link_ec_grtr_R_Z : ChainLink (EqualChain R) (GreaterRel * Z) (GreaterChain R) :=
  fun ecx ln => link_ec_grtr R ecx (snd_map IZR ln).
#[export] Instance link_gc_eq_Z_R : ChainLink (GreaterChain Z) (EqualRel * R) (GreaterChain R) := 
  fun gcn x => link_gc_eq R (gc_map IZR gcn) x.
#[export] Instance link_gc_eq_R_Z : ChainLink (GreaterChain R) (EqualRel * Z) (GreaterChain R) := 
  fun gcx ln => link_gc_eq R gcx (snd_map IZR ln).
#[export] Instance link_gc_grtr_Z_R : ChainLink (GreaterChain Z) (GreaterRel * R) (GreaterChain R) := 
  fun gcn lx => link_gc_grtr R (gc_map IZR gcn) lx.
#[export] Instance link_gc_grtr_R_Z : ChainLink (GreaterChain R) (GreaterRel * Z) (GreaterChain R) := 
  fun gcx ln => link_gc_grtr R gcx (snd_map IZR ln).