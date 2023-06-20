(******************************************************************************)
(*                  This file is part of Waterproof-lib.                      *)
(*                                                                            *)
(*   Waterproof-lib is free software: you can redistribute it and/or modify   *)
(*    it under the terms of the GNU General Public License as published by    *)
(*     the Free Software Foundation, either version 3 of the License, or      *)
(*                    (at your option) any later version.                     *)
(*                                                                            *)
(*     Waterproof-lib is distributed in the hope that it will be useful,      *)
(*      but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*       MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the         *)
(*               GNU General Public License for more details.                 *)
(*                                                                            *)
(*     You should have received a copy of the GNU General Public License      *)
(*   along with Waterproof-lib. If not, see <https://www.gnu.org/licenses/>.  *)
(*                                                                            *)
(******************************************************************************)

Require Import Sets.Ensembles. 

Require Import Notations.Common.

Unset Auto Template Polymorphism.
Record subset (X : Type) := as_subset { pred :> X -> Prop }.

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
  (In _ A x) (at level 50). 

Notation "x ∉ A" :=  
  (~ In _ A x) (at level 50). 

Notation "A ⊂ B" := 
  (Included _ A B) (at level 45). 
  
Notation "A 'and' B 'are' 'disjoint'" := 
  (Disjoint _ A B) (at level 50).   
  
Notation "｛ x : T | P ｝" := 
  (fun (x : T) ↦ P) (x at level 99).

Declare Scope subset_scope.
Notation "x : A" := ((pred _ A) x) (at level 70, no associativity) : subset_scope.