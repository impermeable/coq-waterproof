From Waterproof Require Import Waterproof.
From Waterproof Require Import Tactics.
From Waterproof Require Import Notations.Sets.

(* Test 0: Test if grammar functions*)
Goal 0 = 0.
Proof.
    We conclude that (0 = 0). 
Abort.


(* Test 1: Missing capital letter at beginning *)
Goal 0 = 0.
Proof.
    we conclude that (0 = 0).
Abort.

(* Test 2: Missing letter in first word *)
Goal 0 = 0.
Proof.
    W conclude that (0 = 0).
Abort.

(* Test 3: Missing letter in second word *)
Goal 0 = 0.
Proof.
    We conclde that (0 = 0).
Abort.

(* Test 4: Missing letter in third word *)
Goal 0 = 0.
Proof.
    We conclude tht 0 = 0.
Abort.

(* Test 5: Spelling error in first word *)
Goal 0 = 0.
Proof.
    Wo conclude that (0 = 0).
Abort.

(* Test 6: Spelling error in second word *)
Goal 0 = 0.
Proof.
    We conclade that (0 = 0).
Abort.

(* Test 7: Spelling error in third word *)
Goal 0 = 0.
Proof.
    We conclude thot (0 = 0).
Abort.

(* Test 8: Spelling error after expression *)
Goal 0 = 0.
Proof.
    Either 0 > 1 ar 0 ≤ 1.
Abort.

(* Test 9: Missing first word *)
Goal 0 = 0.
Proof.
    conclude that (0 = 0).
Abort.

(* Test 10: Missing second word *)
Goal 0 = 0.
Proof.
    We that (0 = 0).
Abort.

(* Test 11: Missing third word *)
Goal 0 = 0.
Proof.
    It holds (0 = 0).
Abort.

(* Test 12: Missing first paren *)
Goal (0 = 0) -> True.
Proof.
    Assume that (0 = 0) i).
Abort.

(* Test 13: Missing second paren *)
Goal (0 = 0) -> True.
Proof.
    Assume that (0 = 0) (i.
Abort.

(* Test 14: Missing both parens *)
Goal (0 = 0) -> True.
Proof.
    Assume that (0 = 0) i.
Abort.

(* Test 15: Missing period *)
Goal (0 = 0) -> True.
Proof.
    Assume that (0 = 0)
Abort.

(* Test 16: Missing right paren in expression *)
Goal ((0 + 1) * 1 = 0) -> True.
Proof.
    Assume that ((0 + 1 * 1).
Abort.

(* Test 17: Missing left paren in expression *)
Goal ((0 + 1) * 1 = 0) -> True.
Proof.
    Assume that (0 + 1) * 1).
Abort.


(* Test 18: Wrong symbol *)
Lemma test18 (a : nat) (A B : subset nat) : (a ∈ B) -> True.
Proof.
    Assume that (a ⊂ A).
Abort.
















