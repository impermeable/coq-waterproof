(** ** Standard mathematical function notation. *)
Notation " f ( x , .. , y )" := (.. (f x) .. y) 
  (at level 10,
  format "f '(' x ,  .. ,  y ')'") : type_scope.

(** ** Quantifiers
  Allow unicode characters ∀ and ∃ for readability.
*)
Notation "'for' 'all' x .. y , P" := (forall x, .. (forall y, P) ..)
  (at level 200, x binder, y binder, right associativity,
  format "'[ ' '[ ' for  all  x .. y ']' , '//'  P ']'") : type_scope.

Notation "∀ x .. y , P" := (forall x, .. (forall y, P) ..)
  (at level 200, x binder, y binder, right associativity,
  only parsing) : type_scope.

Notation "'there' 'exists' x .. y , P " := (exists x, .. (exists y, P) ..)
  (at level 200, x binder, y binder, right associativity,
  format "'[ ' '[ ' there  exists  x .. y ']' , '//'  P ']'") : type_scope.

Notation "∃ x .. y , P " := (exists x, .. (exists y, P) ..)
  (at level 200, x binder, y binder, right associativity,
  only parsing) : type_scope.

Notation "'fun' x .. y '↦' t" := (fun x => .. (fun y => t) ..)
  (at level 200, x binder, y binder, right associativity,
  format "'[ ' '[ ' 'fun' x .. y ']' '↦' '/' t ']'") : type_scope.

(** ** Set symbols, implications
  The following notations deal with sets.
*)
Notation "x ∨ y" := (x \/ y) (at level 85, right associativity) : type_scope.
Notation "x ∧ y" := (x /\ y) (at level 80, right associativity) : type_scope.

Notation "x → y" := (x -> y) (at level 99, y at level 200, right associativity, only parsing): type_scope.

Notation "x ⇒ y" := (x -> y) (at level 99, y at level 200, right associativity, only parsing): type_scope.

Notation "x ⇨ y" := (x -> y) (at level 99, y at level 200, right associativity): type_scope.

Notation "x ↔ y" := (x <-> y) (at level 95, no associativity): type_scope.
Notation "x ⇔ y" := (x <-> y) (at level 95, no associativity): type_scope.
Notation "¬ x" := (~x) (at level 75, right associativity) : type_scope.

Notation "'Show' 'a' 'contradiction' 'by:' '(1)' 'Showing' 'that' 'both' 'P' 'and' '¬P' 'hold' 'for' 'some' 'statement' 'P.' '(2)' 'Writing' '‘Contradiction.‘' 'or' '‘↯.‘.'" := (False)
  (only printing, format "'[ ' Show  a  contradiction  by: ']' '//' (1)  Showing  that  both  P  and  ¬P  hold  for  some  statement  P. '//' (2)  Writing  ‘Contradiction.‘  or  ‘↯.‘.").