(* Verifies that the [Waterproof Language French.] issued inside Waterproof.French
   does NOT propagate through Require Import: without issuing the command here,
   messages stay English. *)
Require Import Ltac2.Ltac2.
Require Import Waterproof.Automation.
Require Import Waterproof.French.
Require Import Waterproof.Util.Assertions.

Waterproof Enable Automation RealsAndIntegers.
Waterproof Enable Redirect Errors.

Goal (0 = 1).
  let result () := Nous concluons que (0 = 1) in
  assert_fails_with_string result "Could not verify that (0 = 1).".
Abort.
