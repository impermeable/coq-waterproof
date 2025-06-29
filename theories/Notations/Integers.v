Require Import Coq.ZArith.BinInt.
Require Import Coq.ZArith.Zeven.
Require Import Libs.Integers.Square.

Open Scope Z_scope.

Notation "a | b" := (Z.divide a b) (at level 70).

Notation "a 'is' 'even'" := (Zeven a) (at level 70).
Notation "a 'is' 'odd'" := (Zodd a) (at level 70).

Notation "n ²" := (square n) (at level 1) : Z_scope.
