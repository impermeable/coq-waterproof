Require Import Sets.Ensembles. 

Require Import Notations.Common.

Unset Auto Template Polymorphism.
Record subset (X : Type) := as_subset { pred :> X -> Prop }.

Declare Scope subset_scope.
Notation "x : A" := ((pred _ A) x) (at level 70, no associativity) : subset_scope.

Notation "'subset' U" := 
  (Ensemble U) (at level 50). 

Notation "'set_of_subsets' U" := 
  (Ensemble (Ensemble U)) (at level 50). 

Definition empty {U} := Empty_set U.
Definition full {U} := Full_set U.
Notation "∅" := 
  (empty). 

Notation "'Ω'" := 
  (full) (at level 0). 

Notation "A ∩ B" := 
  (Intersection _ A B) (at level 45). 

Notation "A ∪ B" := 
  (Union _ A B) (at level 45). 

Notation "A \ B" := 
  (Setminus _ A B) (at level 45). 

Notation "x ∈ A" := 
  (In _ A x) (at level 50) : subset_scope. 

Notation "x ∉ A" :=  
  (~ In _ A x) (at level 50). 

Notation "A ⊂ B" := 
  (Included _ A B) (at level 45). 
  
Notation "A 'and' B 'are' 'disjoint'" := 
  (Disjoint _ A B) (at level 50).   
  
Notation "｛ x : T | P ｝" := 
  (fun (x : T) ↦ P) (x at level 99).