(* Require Import Lia. *)
(* Is this the right import, could be less heavy maybe *)
(* Require Import Arith. *)

Declare Scope big_scope.

Open Scope big_scope.

(* Code lifted from mathcomp *)

(* Variables (R : Type). *)
Variant bigbody R I := BigBody of I & (R → R → R) & bool & R.

Definition applybig {R I} (body : bigbody R I) x :=
  let: BigBody _ op b v := body in if b then op v x else x.

Definition reducebig R I idx r (body : I → bigbody R I) :=
  foldr (applybig \o body) idx r.

Canonical bigop_unlock := Unlockable bigop.unlock.

Definition index_iota m n := iota m (n - m).

Lemma mem_index_iota m n i : i \in index_iota m n = (m ≤ i < n).
