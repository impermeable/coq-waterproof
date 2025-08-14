(******************************************************************************)
(*                  This file is part of Waterproof-lib.                     *)
(*                                                                            *)
(*   Waterproof-lib is free software: you can redistribute it and/or modify  *)
(*    it under the terms of the GNU General Public License as published by   *)
(*     the Free Software Foundation, either version 3 of the License, or     *)
(*                    (at your option) any later version.                    *)
(*                                                                            *)
(*     Waterproof-lib is distributed in the hope that it will be useful,     *)
(*      but WITHOUT ANY WARRANTY; without even the implied warranty of       *)
(*       MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the        *)
(*               GNU General Public License for more details.                *)
(*                                                                            *)
(*     You should have received a copy of the GNU General Public License     *)
(*   along with Waterproof-lib. If not, see <https://www.gnu.org/licenses/>. *)
(*                                                                            *)
(******************************************************************************)

Require Import Waterproof.Libs.Functions.
Require Import Waterproof.Notations.Sets.

Open Scope subset_scope.

(** * Notations for function images *)

(** The notation g[U] for the image of set U under function g *)
Notation "g [ U ]" := (function_image g U) (at level 10) : subset_scope.

(** Alternative notation for function composition (if needed) *)
(* Notation "g ∘ f" := (fun x => g (f x)) (at level 40, left associativity) : function_scope. *)
