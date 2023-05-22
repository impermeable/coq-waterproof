Require Import Ltac2.Ltac2.

Require Import Waterproof.Waterproof.
Require Import Waterproof.Automation.
Require Import Waterproof.Notations.
Require Import Waterproof.Tactics.

Open Scope nat_scope.
(* Test 0: check if notations work. *)

Goal  ∀ n : ℕ -> ℕ, (∀ k : ℕ, (n (k + 1) > n k)%nat) ⇒
    ∀ k : ℕ, (n k ≥ k)%nat.
intro n.
intro H.
induction k as [| k IHk].
- solve [auto with wp_integers].
- assert (H1 : S k = k + 1) by (auto with wp_integers).
  rewrite H1.
  assert (H2 : n (k + 1) > n k) by (auto with wp_integers).
  auto with wp_integers. 
Qed.

Require Import Lia.
Goal (& 3 < 4 <= 5).
solve [auto with wp_core wp_integers].
Qed.

Goal (& 3 = 3 = 3).
solve [auto with wp_core wp_integers].
Qed.

(* Test 1: check if terms of a subset can be coerced to terms of the underlying set (here: [R]). *)
Goal forall x : nat, (& x < 5 = 2 + 3) -> (x < 5).
intro x.
intro H.
simpl_ineq_chains ().
solve [auto with wp_integers].
Qed.