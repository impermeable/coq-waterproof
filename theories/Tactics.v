Require Export Ltac2.Ltac2.

Require Import Waterproof.
Require Export Tactics.Assume.

Ltac2 @ external wauto: int -> unit := "coq-waterproof" "wauto".