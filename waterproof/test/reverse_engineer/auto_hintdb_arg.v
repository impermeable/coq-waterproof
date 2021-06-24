(** * [auto_hintdb_arg.v]
Authors: 
    - Lulof Pirée (1363638)

Creation date: 23 June 2021

Experiment to find out semantics of the database
argument to [Std.auto]. 
Which value is needed for the default (i.e. only [core]),
and which value to achieve [with *]?

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
(** Source code:

* Notations.v
Ltac2 Notation "auto" n(opt(tactic(0)))
    use(opt(seq("using", list1(thunk(constr), ","))))
    dbs(opt(seq("with", hintdb))) := auto0 n use dbs.

Ltac2 default_db dbs := match dbs with
| None => Some []
| Some dbs =>
  match dbs with
  | None => None
  | Some l => Some l
  end
end.

* Std.v
Ltac2 @ external auto : debug -> int option -> 
    (unit -> constr) list -> ident list option -> 
    unit := "ltac2" "tac_auto".
*)

Ltac2 Notation "fake_auto" dbs(opt(seq("with", hintdb))) 
    := default_db dbs.

(* To use the default, i.e. [core], 
    pass [Some ([])] to Std.auto
    
    Evidence: the following gives:
    [Some ([])]
*)
Ltac2 Eval fake_auto.

(* To use [with *], 
    i.e. all imported databases that Coq can find, 
    pass [None] to Std.auto
    
    Evidence: the following gives:
    ['a list option = None]
*)
Ltac2 Eval fake_auto with *.

(* To use [with somedb], 
    pass a list of idents
    (e.g. [Some ((@somedb)::[])]) to Std.auto.
    
    Evidence: the following gives:
    [ident list option = Some ([@nocore])]
*)
Ltac2 Eval fake_auto with nocore.