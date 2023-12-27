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

Require Import Ltac2.Ltac2.

Require Import Waterproof.Waterproof.
Require Import Waterproof.Automation.
Require Import Waterproof.Notations.
Require Import Waterproof.Tactics.

Open Scope nat_scope.
(* Test 0: check if notations work. *)

Require Import Lia.

Goal  ∀ n : ℕ -> ℕ, (∀ k : ℕ, (n (k + 1) > n k)%nat) ⇒
    ∀ k : ℕ, (n k ≥ k)%nat.
  intro n.
  intro H.
  induction k as [| k IHk].
  - solve [auto with wp_integers zarith].
  - assert (H1 : S k = k + 1) by (auto with wp_integers zarith).
    rewrite H1.
    assert (H2 : n (k + 1) > n k) by (auto with wp_integers zarith).
    auto with wp_integers zarith. 
Qed.

Require Import Lia.
Goal (& 3 < 4 <= 5).
  cbn; repeat split; solve [ltac1:(auto with wp_core wp_integers)].
Qed.

Goal (& 3 = 3 = 3).
  cbn; repeat split; solve [auto with wp_core wp_integers].
Qed.

(* Test 1: check if terms of a subset can be coerced to terms of the underlying set (here: [R]). *)
Goal forall x : nat, (& x < 5 = 2 + 3) -> (x < 5).
  intro x.
  intro H.
  simpl_ineq_chains ().
  solve [auto with wp_integers zarith].
Qed.