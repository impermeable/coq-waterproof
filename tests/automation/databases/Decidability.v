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

Require Import Waterproof.Waterproof.
Require Import Waterproof.Automation.

Goal forall P : Prop, {P} + {~P}.
Proof.
  ltac2: auto with wp_decidability_epsilon.
Qed.

Goal forall P Q : Prop, P \/ Q -> {P} + {Q}.
Proof.
  ltac2: auto with wp_decidability_epsilon.
Qed.

Goal forall P : Prop, P \/ ~P.
Proof.
  ltac2: auto with wp_decidability_classical.
Qed.

Goal forall P Q : Prop, {P} + {Q} -> P \/ Q.
  ltac2: auto with wp_decidability_constructive.
Qed.

Goal forall P Q : Prop, {Q} + {P} -> Q \/ P.
  ltac2: auto with wp_decidability_constructive.
Qed.

Goal forall P Q R: Prop, {P} + {Q} + {R} -> P \/ Q \/ R.
  ltac2: auto with wp_decidability_constructive.
Qed.

Goal forall P Q R: Prop, {P} + {R} + {Q} -> P \/ Q \/ R.
  ltac2: auto with wp_decidability_constructive.
Qed.

Goal forall P Q R: Prop, {Q} + {P} + {R} -> P \/ Q \/ R.
  ltac2: auto with wp_decidability_constructive.
Qed.

Goal forall P Q R: Prop, {Q} + {R} + {P} -> P \/ Q \/ R.
  ltac2: auto with wp_decidability_constructive.
Qed.

Goal forall P Q R: Prop, {R} + {P} + {Q} -> P \/ Q \/ R.
  ltac2: auto with wp_decidability_constructive.
Qed.

Goal forall P Q R: Prop, {R} + {P} + {Q} -> P \/ Q \/ R.
  ltac2: auto with wp_decidability_constructive.
Qed.

Goal forall n : nat, n < 5 \/ n > 4.
Proof.
  ltac2: intro n.
  ltac2: auto with wp_decidability_nat.
Qed.

From Stdlib Require Import Reals.Reals.
Open Scope R_scope.
Goal forall x : R, x < 5 \/ x > 4.
Proof.
  ltac2: intro x.
  ltac2: auto with wp_decidability_reals.
Qed.
