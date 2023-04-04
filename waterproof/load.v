(** * Module for loading databases
Authors: 
    - Jim Portegies
Creation date: 29 Mar 2023

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
Require Import Waterproof.selected_databases.
Require Import Waterproof.populate_database.

(** The module type db_config determines what should be in
    database configuration files.

    When defining your own databases, you need to give
    definitions for all the corresponding fields below.
*)
Module Type db_config.
(** The preload_module should be a module of module type preloader, 
    and can be used to put lemmas in Coq hint databases. *)
Declare Module preload_module : preloader.
(** The following Ltac2 variables can be filled 
    with lists of identifiers of Coq hint databases. *)
Ltac2 global_databases () := ([] : ident list).
Ltac2 decidability_databases () := ([] : ident list).
Ltac2 negation_databases () := ([] : ident list).
Ltac2 first_attempt_databases () := ([] : ident list).
(** The boolean append_databases determines whether 
    the new databases should be appended, or whether they 
    should replace the list of databases. *)
Ltac2 append_databases := true.
End db_config.

(** The module databases takes in a database config file
    (i.e. a module of module type db_config) and produces 
    the module that actually loads the databases.

    In turn, that module can be loaded.
*)
Module databases(X : db_config).
Export X.preload_module.
Ltac2 Set global_database_selection as old_selection := 
    fun () =>
        if X.append_databases
            then List.concat ((X.global_databases ())::(old_selection ())::[])
            else X.global_databases ().
Ltac2 Set global_negation_database_selection as old_selection :=
    fun () => 
        if X.append_databases
            then List.concat ((X.negation_databases ())::(old_selection ())::[])
            else X.negation_databases ().
Ltac2 Set global_decidability_database_selection as old_selection :=
    fun () =>
        if X.append_databases
            then List.concat ((X.decidability_databases ())::(old_selection ())::[])
            else X.decidability_databases ().
Ltac2 Set global_first_attempt_database_selection as old_selection :=
    fun () =>
        if X.append_databases
            then List.concat ((X.first_attempt_databases ())::(old_selection ())::[])
            else X.first_attempt_databases ().
End databases.

(** ** Preset database configuration files
    (i.e. modules of module Type db_config) *)

(** Database configuration file RealsAndIntegers. *)
Module RealsAndIntegers <: db_config.
Module preload_module := wp_all.
Ltac2 append_databases := true.
Ltac2 global_databases () := [ @arith; @zarith; @real; @wp_core; @wp_classical_logic; @wp_constructive_logic; @wp_integers; @wp_reals; @wp_subsets].
Ltac2 decidability_databases () := [ @nocore; @wp_decidability_nat; @wp_decidability_reals].
Ltac2 negation_databases () := [ @nocore; @wp_negation_nat; @wp_negation_int; @wp_negation_reals].
Ltac2 first_attempt_databases () := [ @core; @wp_subsets; @wp_classical_logic].
End RealsAndIntegers.

(** Database configuration file Integers. *)
Module Integers <: Waterproof.load.db_config.
Module preload_module := Waterproof.populate_database.wp_all.
Ltac2 append_databases := true.
Ltac2 global_databases () := [ @arith; @zarith; @wp_core; @wp_classical_logic; @wp_constructive_logic; @wp_integers].
Ltac2 decidability_databases () := [ @nocore; @wp_decidability_nat].
Ltac2 negation_databases () := [ @nocore; @wp_negation_nat; @wp_negation_int].
Ltac2 first_attempt_databases () := [ @core; @wp_classical_logic].
End Integers.

(** Database configuration file Intuition. *)
Module Intuition <: Waterproof.load.db_config.
Module preload_module := Waterproof.populate_database.wp_intuition.
Ltac2 append_databases := true.
Ltac2 global_databases () := [ @wp_intuition].
Ltac2 decidability_databases () := [].
Ltac2 negation_databases () := [].
Ltac2 first_attempt_databases () := [].
End Intuition.

(** Database configuration file Intuition. *)
Module Sets <: Waterproof.load.db_config.
Module preload_module := Waterproof.populate_database.wp_sets.
Ltac2 append_databases := true.
Ltac2 global_databases () := [ @wp_sets].
Ltac2 decidability_databases () := [].
Ltac2 negation_databases () := [].
Ltac2 first_attempt_databases () := [].
End Sets.

(** Reset global database variables. *)

Ltac2 Set global_database_selection := fun () => ([]:ident list).
Ltac2 Set global_negation_database_selection := fun () => ([]:ident list).
Ltac2 Set global_decidability_database_selection := fun () => ([]:ident list).
Ltac2 Set global_first_attempt_database_selection := fun () => ([]:ident list).
