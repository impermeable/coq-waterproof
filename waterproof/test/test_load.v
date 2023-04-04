(** * Testcases for changing the global variable [global_database_selection]
Authors: 
    - Jim Portegies
Creation date: 3 April 2023

Test whether the loading works as intended in the Waterproof.load module.

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
Require Import Waterproof.test_auxiliary.
Require Import Waterproof.init_automation_global_variables.
Require Import Waterproof.load.

(** Test whether length of global database selection is zero*)
Goal False.
assert_list_equal Ident.equal Message.of_ident (global_database_selection ()) ([]).
Abort.

Module TestDBConfig <: Waterproof.load.db_config.
Module preload_module := Waterproof.populate_database.wp_all.
Ltac2 append_databases := true.
Ltac2 global_databases () := [ @test_global_1; @test_global_2].
Ltac2 decidability_databases () := [ @test_dec_1; @test_dec_2; @test_dec_3].
Ltac2 negation_databases () := [ @test_neg_1].
Ltac2 first_attempt_databases () := [].
End TestDBConfig.

(** Test: Before importing a db_config module, the global database selection should 
    still be empty *)
Goal False.
assert_list_equal Ident.equal Message.of_ident
    (global_database_selection ()) ([]).
Abort.

Module Import test_database := Waterproof.load.databases(TestDBConfig).

(** Test: After importing the test_database module, the global database selection 
    should be [ @test_global_1; @test_global_2]*)
Goal False.
assert_list_equal Ident.equal Message.of_ident
    (global_database_selection ()) ([ @test_global_1; @test_global_2]).
Abort.

Module ClearDBConfig <: Waterproof.load.db_config.
Module preload_module := Waterproof.populate_database.wp_all.
Ltac2 append_databases := false.
Ltac2 global_databases () := [].
Ltac2 decidability_databases () := [].
Ltac2 negation_databases () := [].
Ltac2 first_attempt_databases () := [].
End ClearDBConfig.

Module Import test_clear_database := Waterproof.load.databases(ClearDBConfig).
(* Import test_clear_database.*)

(** Test: database lists should be empty now. *)
Goal False.
assert_list_equal Ident.equal Message.of_ident
    (global_database_selection ()) ([]).
assert_list_equal Ident.equal Message.of_ident
    (global_decidability_database_selection ()) ([]).
assert_list_equal Ident.equal Message.of_ident
    (global_negation_database_selection ()) ([]).
assert_list_equal Ident.equal Message.of_ident
    (global_first_attempt_database_selection ()) ([]).
Abort.

Module Import db_Integers := databases(Integers).

(** Test: database selection should be equal to that of the Integers. *)
Goal False.
assert_list_equal Ident.equal Message.of_ident
    (global_database_selection ()) ([ @arith; @zarith; @wp_core; @wp_classical_logic; @wp_constructive_logic; @wp_integers]).
Abort.

Module Import db_Intuition := databases(Intuition).

(** Test: database selection should now have those of Intuition added. *)
Goal False.
assert_list_equal Ident.equal Message.of_ident
    (global_database_selection ()) ([ @wp_intuition; @arith; @zarith; @wp_core; @wp_classical_logic; @wp_constructive_logic; @wp_integers]).
Abort.
