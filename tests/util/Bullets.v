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

From Waterproof Require Import Tactics.
From Waterproof Require Import Notations.Common.

Set Default Goal Selector "!".

Local Parameter A : Prop.
Local Parameter w : A.
Set Bullet Behavior "Waterproof Relaxed Subproofs".

Goal (A ∧ A ∧ A ∧ A).
Proof.
repeat split.
- exact w.
- exact w.
- exact w.
- exact w.
Qed.

Goal (True ∧ True) ∧ (True ∧ True).
Proof.
+++ split.
-- {split.
  * + -- exact I.
  * exact I. }
-- split.
  -- + -- exact I.
  -- exact I.
Qed.

Goal (A ∧ A) ∧ (A ∧ A) ∧ (A ∧ A ∧ A).
Proof.
split.
{ - split.
    - exact w.
    - exact w. }
split.
+ split.
  Fail exact w.
  - exact w.
  * exact w.
+ split.
  { exact w. }
  - split.
    { exact w. }
    exact w.
Qed.
