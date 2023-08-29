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

Require Import Util.Goals.

(**
  Defines a variable in an arbitrary goal.

  Arguments:
    - [u: constr], the name of the variable.
    - [t: constr], the variable to be defined.

  Does:
    - defines [t] as [u].
*)
Local Ltac2 defining (u: ident) (t: constr) :=
  set ($u := $t);
  let u_constr := Control.hyp u in 
  let w := Fresh.fresh (Fresh.Free.of_goal ()) @_defeq in
  assert ($w : $u_constr = $t) by reflexivity.
    


Ltac2 Notation "Define" u(ident) ":=" t(constr) :=
  panic_if_goal_wrapped ();
  defining u t.