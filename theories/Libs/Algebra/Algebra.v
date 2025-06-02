Section Monoid.

Variables (T : Type).

Structure CommSemiRing : Type := 
    { add : T -> T -> T
    ; mul : T -> T -> T
    ; zero : T
    ; one : T
    ; add_comm : forall t s, add t s = add s t
    ; add_assoc : forall t s u, add t (add s u) = add (add t s) u
    ; zero_add : forall t, add zero t = t 
    ; one_mul : forall t, mul one t = t
    ; left_distrib : forall t s u, mul t (add s u) = add (mul t s) (mul t u)
    }.

End Monoid.