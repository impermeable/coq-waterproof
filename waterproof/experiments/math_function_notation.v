Variable g : nat * nat -> bool.
Variable n m : nat.
Check g(n,m).

Notation " f ( x , .. , y )" := (.. (f x) .. y) 
(at level 10) : type_scope.

Variable dist : nat -> nat -> nat.
Variable foo : nat -> bool -> nat * nat.

Check dist(n,m).
Check (n,m).

Check foo (dist(n,m), false).
Check foo (dist(n,m)) false.
Check foo (dist n m) false.

Check dist(n).
Check dist(n)(m).

Goal dist(n,m) = dist n m.
Proof. reflexivity. Qed.

Require Import Reals.
Print is_lub.
