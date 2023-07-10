Require Import Waterproof.Waterproof.
Require Import Waterproof.Waterprove.
Require Import Ltac2.Ltac2.

Goal 0 = 0.
print_warning_ffi (Message.of_string "This is the warning to be printed").
Abort.