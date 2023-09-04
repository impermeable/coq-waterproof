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

Require Import Coq.Reals.Reals.

Require Import Waterproof.Automation.
Require Import Waterproof.Notations.
Require Import Waterproof.Tactics.

Waterproof Enable Automation RealsAndIntegers.
Waterproof Enable Automation Intuition.

Require Import Waterproof.Libs.Analysis.SupAndInf.

Open Scope R_scope.



(** Tests for using propositional definitions. *)

(* Test 1: expanding definition in goal. *)
Goal [0,1] is non-empty.
Proof.
  By definition_non_empty it suffices to show that (there exists x : R, [0,1] x).
Abort.

(* Test 2: expanding definition in hypothesis. *)
Goal there exists x : R, [0,1] x.
Proof.
  By definition_non_empty it suffices to show that ([0,1] is non-empty).
Abort.

(* Test 3a: expand larger definition in goal *)
Goal sup [0,1] = 1.
Proof.
  assert ([0,1] is non-empty) by admit.
  assert ([0,1] is bounded from above) by admit.
  Time By definition_supremum it suffices to show that 
    (1 is an upper bound for [0,1] 
      ∧ (for all L : R, L is an upper bound for [0,1] -> 1 <= L)).
Abort.

(* Test 3b: expand larger definition in hyp *)
Goal sup [0,1] = 1 -> False.
Proof.
  intro H.
  assert ([0,1] is non-empty) by admit.
  assert ([0,1] is bounded from above) by admit.
  Time By definition_supremum it holds that 
    (1 is an upper bound for [0,1] 
      ∧ (for all L : R, L is an upper bound for [0,1] -> 1 <= L)).
Abort.


(** Tests for using definition when it is added as a hint,
  so definitions do not need to be mentioned explicitly. *)
Section DefAddedToHints.
#[local] Hint Resolve definition_non_empty : wp_reals.

(* Test 4: no definition needed for expanding of goal  *)
Goal [0,1] is non-empty.
Proof.
  It suffices to show that (there exists x : R, [0,1] x).
Abort.

(* Test 5: no definition needed for expanding of hypothesis *)
Goal [0,1] is non-empty.
Proof.
  It suffices to show that (there exists x : R, [0,1] x).
Abort.

(* Test 6: mentioning correct definition is not punished by restricted automated proof search.  *)
Goal [0,1] is non-empty.
Proof.
  Fail By definition_upper_bound it suffices to show that (there exists x : R, [0,1] x).
  By definition_non_empty it suffices to show that (there exists x : R, [0,1] x).
Abort.
End DefAddedToHints.


(** Tests for expanding definitions. *)

(* Test 7: non-empty *)
Goal False.
Proof.
  Expand the definition of non-empty in ([0,1] is non-empty).
  Expand the definition of non-empty in (bound [0,1]).
Abort.

(*Test 8: is upper bound *)
Goal False.
Proof. 
  Expand the definition of upper bound in (1 is an upper bound for [0,1]).
Abort.

(* Test 9: bounded from above *)
Goal False.
Proof. 
  Expand the definition of bounded from above in ([0,1] is bounded from above).
Abort.

(* Test 10 : bounded from below *)
Goal False.
Proof. 
  Expand the definition of bounded from below in ([0,1] is bounded from below).
Abort.

(* Test 11: supremum *)
Goal False.
  Expand the definition of supremum in (sup [0,1]).
  Expand the definition of supremum in (1 = sup [0,1]).
Abort.

(* Test 12: infimum *)
Goal False.
  Expand the definition of inf in (inf [0,1]).
  Expand the definition of inf in (0 = inf [0,1]).
  Expand the definition of infimum in (sup [0,1]).
Abort.


(** Test using properties of supremum *)

(* Test 13: supremum is an upper bound *)
Goal False.
Proof.
  We claim that ([0,1] is non-empty). { admit. }
  We claim that ([0,1] is bounded from above). { admit. }
  By definition_supremum it holds that (sup [0,1] is an upper bound for [0,1]).
Abort.

(* Test 14: (Advanced) Supremum behaves as upper bound. Skips having to expand definition upper bound. *)
Section AdvancedSupLemma.
#[local] Hint Resolve _sup_behaves_as_bound : wp_reals.

Goal False.
Proof.
  We claim that ([0,1] is non-empty). { admit. }
  We claim that ([0,1] is bounded from above). { admit. }
  We claim that ([0,1] 0). { admit. }
  By definition_supremum it holds that (0 <= sup [0,1]).
Abort.
End AdvancedSupLemma.