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

(* Very important coding rule:
 - This file needs to be loaded first in all of waterproof files.
 - It is forbidden to require ltac2, except if you know what you are doing.
 *)
From Ltac2 Require Export Ltac2.

Declare ML Module "coq-waterproof.plugin".


(* Reverse escape hatch *)
Ltac2 Notation "wp:" x(waterproof_tactic) := x.


(* This tells Rocq to use the Waterproof tactic mode when in a proof. *)
#[export] Set Default Proof Mode "Waterproof".

(* This tells Ltac2 Notation to put new parsing rules in the
   waterproof non-terminal symbol. *)
#[export] Set Ltac2 Default Notation Entry "Waterproof.Waterproof.waterproof_tactic".

#[export] Set Ltac2 Default Notation Entry Level 5.

(* Default scape hatch to ltac2 *)
Ltac2 Notation "ltac2:" x(tactic) := x.
