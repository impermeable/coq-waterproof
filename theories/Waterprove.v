Require Import Ltac2.Ltac2.

Require Import Waterproof.

Ltac2 @ external waterprove: Init.int -> Init.bool -> (Init.unit -> Init.constr) Init.list -> Init.string -> Init.unit := "coq-waterproof" "waterprove".
