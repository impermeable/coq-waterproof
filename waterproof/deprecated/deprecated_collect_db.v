(** # **Collect all databases**

Authors: 
    - Adrian Vramulet
    - Tudor Voicu
    - Lulof Pirée (1363638)
Creation date: 14 June 2021

Deprecated method of collecting all databases
and running [auto ] on them.

--------------------------------------------------------------------------------

This file is part of Waterproof-lib.

Waterproof-lib is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

Waterproof-lib is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with Waterproof-lib.  If not, see <https://www.gnu.org/licenses/>.
*)

From Ltac2 Require Import Ltac2.
From Ltac2 Require Option.
From Ltac2 Require Import Message.
Require Import Waterproof.databases.

Local Ltac2 unwrap_cons x l :=
  match x with
  | None => l
  | Some y => y :: l
  end.

Local Ltac2 collect_all_db () :=
  let l :=
      unwrap_cons (of_string "nocore") (unwrap_cons (of_string "eq_general") [])
  in
  let l := match! goal with
           | [ |- context [0] ] => unwrap_cons (of_string "eq_opp") l
           | [ |- _ ] => l
           end
  in
  let l := match! goal with
           | [ |- context [1] ] => unwrap_cons (of_string "eq_zero") l
           | [ |- _ ] => l
           end
  in
  let l := match! goal with
           | [ |- context [2] ] => unwrap_cons (of_string "eq_one") l
           | [ |- _ ] => l
           end
  in
  let l := match! goal with
           | [ |- context [3] ] => unwrap_cons (of_string "eq_abs") l
           | [ |- _ ] => l
           end
  in
  let l := match! goal with
           | [ |- context [4] ] => unwrap_cons (of_string "eq_sqr") l
           | [ |- _ ] => l
           end
  in
  let l := match! goal with
           | [ |- context [5] ] => unwrap_cons (of_string "eq_exp") l
           | [ |- _ ] => l
           end
  in
  let l := match! goal with
           | [ |- context [6] ] => unwrap_cons (of_string "eq_other") l
           | [ |- _ ] => l
           end
  in
  let l := match! goal with
           | [ |- context [7] ] => unwrap_cons (of_string "eq_plus") l
           | [ |- _ ] => l
           end
  in
  let l := match! goal with
           | [ |- context [8] ] => unwrap_cons (of_string "eq_minus") l
           | [ |- _ ] => l
           end
  in
  let l := match! goal with
           | [ |- context [9] ] => unwrap_cons (of_string "eq_mult") l
           | [ |- _ ] => l
           end
  in
  l.

Ltac2 myauto(a:int) :=
  let var := collect_all_db () in
  solve[ auto0 (Some a) None (Some (Some var)) ].