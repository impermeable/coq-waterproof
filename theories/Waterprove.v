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

Require Export Ltac2.Ltac2.

Require Import Waterproof.

Require Import Ltac2.Bool.
Require Import Ltac2.Init.

Local Ltac2 Type database_type_ffi.

Local Ltac2 @ external database_type_main: unit -> database_type_ffi := "coq-waterproof" "database_type_main".
Local Ltac2 @ external database_type_decidability: unit -> database_type_ffi := "coq-waterproof" "database_type_decidability".
Local Ltac2 @ external database_type_shorten: unit -> database_type_ffi := "coq-waterproof" "database_type_shorten".

Local Ltac2 @ external waterprove_ffi: int -> bool -> (unit -> constr) list -> database_type_ffi -> unit := "coq-waterproof" "waterprove".
Local Ltac2 @ external rwaterprove_ffi: int -> bool -> (unit -> constr) list -> database_type_ffi -> constr list -> constr list -> unit := "coq-waterproof" "rwaterprove".

Ltac2 @ external print_warning_ffi : message -> unit := "coq-waterproof" "external_print_warning".

Ltac2 Type database_type := [ Main | Decidability | Shorten ].

Local Ltac2 database_type_to_ffi (db_type: database_type): database_type_ffi :=
  match db_type with
    | Main => database_type_main ()
    | Decidability => database_type_decidability ()
    | Shorten => database_type_shorten ()
  end.

Ltac2 contains_shilded_pattern (): bool :=
  lazy_match! goal with
    | [ |- forall _, _ ] => true
    | [ |- exists _, _ ] => true
    | [ |- _ /\ _] => true
    | [ |- _ \/ _] => true
    | [ |- _] => false
  end
.

Ltac2 waterprove (depth: int) (shield: bool) (lems: (unit -> constr) list) (db_type: database_type): unit  :=
  waterprove_ffi depth (shield && contains_shilded_pattern ()) lems (database_type_to_ffi db_type).

Ltac2 rwaterprove (depth: int) (shield: bool) (lems: (unit -> constr) list) (db_type: database_type) (must_use: constr list) (forbidden: constr list): unit  :=
  rwaterprove_ffi depth (shield && contains_shilded_pattern ()) lems (database_type_to_ffi db_type) must_use forbidden.