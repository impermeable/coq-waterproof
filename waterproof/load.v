From Ltac2 Require Import Ltac2.
Require Import Waterproof.selected_databases.
Require Import Waterproof.populate_database.

Module Type db_config.
Declare Module preload_module : preloader.
Ltac2 global_databases () := ([] : ident list).
Ltac2 decidability_databases () := ([] : ident list).
Ltac2 negation_databases () := ([] : ident list).
Ltac2 first_attempt_databases () := ([] : ident list).
End db_config.

Module databases(X : db_config).
Export X.preload_module.
Ltac2 Set global_database_selection as old_selection := 
    fun () => List.concat ((X.global_databases ())::(old_selection ())::[]).
Ltac2 Set global_negation_database_selection as old_selection :=
    fun () => List.concat ((X.negation_databases ())::(old_selection ())::[]).
Ltac2 Set global_decidability_database_selection as old_selection :=
    fun () => List.concat ((X.decidability_databases ())::(old_selection ())::[]).
Ltac2 Set global_first_attempt_database_selection as old_selection :=
    fun () => List.concat ((X.first_attempt_databases ())::(old_selection ())::[]).
End databases.

(** ** Preset database configuration files (i.e. modules) *)

Module RealsAndIntegers <: db_config.
Module preload_module := wp_all.
Ltac2 global_databases () := [ @arith; @zarith; @real; @wp_core; @wp_classical_logic; @wp_constructive_logic; @wp_integers; @wp_reals; @wp_subsets].
Ltac2 decidability_databases () := [ @nocore; @wp_decidability_nat; @wp_decidability_reals].
Ltac2 negation_databases () := [ @nocore; @wp_negation_nat; @wp_negation_int; @wp_negation_reals].
Ltac2 first_attempt_databases () := [ @core; @wp_subsets; @wp_classical_logic].
End RealsAndIntegers.

Module databases_RealsAndIntegers := databases(RealsAndIntegers).
