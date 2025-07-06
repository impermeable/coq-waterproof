Require Import Coq.ZArith.BinInt.
Require Import Coq.ZArith.Zeven.
Require Import Libs.Integers.

Open Scope Z_scope.

Notation "a | b" := (Z.divide a b) (at level 70).
Notation "b 'is' 'divisible' 'by' a" := (Z.divide a b) (at level 70).

Notation "a 'is' 'even'" := (Zeven a) (at level 70).
Notation "a 'is' 'odd'" := (Zodd a) (at level 70).

Notation "n ²" := (square n) (at level 1) : Z_scope.

Notation "n 'is' 'a' 'perfect' 'square'" := (is_square n) (at level 70).

Notation "n 'leaves' 'a' 'remainder' 'of' r 'when' 'divided' 'by' q" := (remainder n q r) (at level 70).
