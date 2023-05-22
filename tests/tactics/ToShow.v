Require Import Ltac2.Ltac2.
Require Import Ltac2.Message.

Require Import Waterproof.Waterproof.
Require Import Waterproof.Automation.
Require Import Waterproof.Tactics.
Require Import Waterproof.Util.Assertions.

(** First test: test all syntax variants **)
Lemma one_is_one: 1 = 1.
Proof.
  We need to show (1 = 1).
  We need to show that (1 = 1).
  We need to show : (1 = 1).
  We need to show that : (1 = 1).
  To show (1 = 1).
  To show that (1 = 1).
  To show that : (1 = 1).
  To show : (1 = 1).
  reflexivity.
Qed.


(** Second test: function definitions are judgementally equal to the function name. 
    So they should be interchangeable. *)
Definition double := fun (x: nat) => 2*x.

Lemma with_function_definition: double 2 = 4.
Proof.
  We need to show (double 2 = 4).
  We need to show (2*2 = 4).
  trivial.
Qed.


(** Third test: this should raise an error, as the wrong goal is supplied. *)
Lemma two_is_two: 2 = 2.
Proof.
  assert_raises_error (fun () => We need to show (1 = 1)).
  reflexivity.
Qed.

(** Fourth test: the goal should be rewritten, if not the proof will fail. *)
Lemma two_is_two_rewrite_goal : 1 + 1 = 1 + 1.
Proof.
  set (k := 2).
  assert (H : k = 2).
  {
    trivial.
  }
  assert_raises_error (fun () => rewrite H).
  We need to show that (k = k).
  rewrite H.
  trivial.
Qed.