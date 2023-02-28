(** * [selected_databases.v]
Authors: 
    - Lulof Pirée (1363638)
    - Cosmin Manea (small additions)
    - Tudor Voice (small additions)
    - Adrian Vrămuleţ (small additions)
Creation date: 14 June 2021

File that hosts the definitions and functions
used to manipulate the global variable
which specifies which databases [wateroprove] uses.

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
From Ltac2 Require Import Option.
From Ltac2 Require Import Message.
Require Import Waterproof.auxiliary.
Require Import Waterproof.databases.

Ltac2 Type WaterproofDatabase := [
    | WaterproofDBAlgebra
    | WaterproofDBMultiplication
    | WaterproofDBPlusMinus
    | WaterproofDBZeroOne
    | WaterproofDBSquareRoot
    | WaterproofDBExponential
    | WaterproofDBAbsoluteValue
    | WaterproofDBRealsAndIntegers
    | WaterproofDBSets
    | WaterproofDBAdditional
    | WaterproofDBReals
    | WaterproofDBSubsets
    | WaterproofDBClassicalLogic
    | WaterproofDBConstructiveLogic
    | WaterproofDBIntegers
    | WaterproofDBIntuition
    | WaterproofDBFirstorder
    (* Databases for manipulating negations. *)
    | WaterproofNegationDBIntegers
    | WaterproofNegationDBReals
    | WaterproofNegationDBRealsAndIntegers
    (* Databases for decidability. *)
    | WaterproofDecidabilityDBReals
    | WaterproofDecidabilityDBNat
].

(** * global_database_selection, global_negation_database_selection
    Global variable that collects a list of database labels
    (of type [WaterproofDatabase]).
    The databases corresponding to these labels will be used
    by the automation function [run_automation] in [waterprove.automation_subroutines],
    which is used in many different tactics.

    Implementation note:
    An [ident list] would have been simpler,
    but Ltac2 does not allow to populate a global variable
    with [ident] literals. 
    Hence the indirection via [WaterproofDatabase] labels.
*)
Ltac2 mutable global_database_selection := ([]:WaterproofDatabase list).
Ltac2 mutable global_negation_database_selection := ([]:WaterproofDatabase list).
Ltac2 mutable global_decidability_database_selection := ([]:WaterproofDatabase list).

(** * global_search_depth
    Global variable that specifies the maximum search depth
    used by the automation tactics (via [run_automation] in [waterprove.automation_subroutines]).
*)
Ltac2 mutable global_search_depth := (2:int).

(** * print_db_loaded 
    Prints "Loading the '...' database."
    where "..." is substituted by the [db_name] argument.
*)
Ltac2 print_db_loaded (db_name: string) :=
    print (concat 
        (concat
            (of_string "Loading the '")
            (of_string db_name)
        )
        (of_string "' database.")
    ).

(** * print_db_loaded 
    Prints "Loading the '...' database."
    where "..." is substituted by the [db_name] argument.
*)
Ltac2 print_search_depth_set_to (new_depth: int) :=
    print (concat 
        (concat
            (of_string "Setting the maximum automation search-depth to ")
            (of_int new_depth)
        )
        (of_string ".")
    ).


(** * load_db_of_label
    Maps a label specifying a database
    to a list of [ident]s that can actually be used to access the database.

    Arguments:
        - [label: WaterproofDatabase], label specifying the list of database
            [ident]s (names) to load.
            Each label generally corresponds to a set of databases
            that are practically always used together.

    Returns:
        - [ident list], list of names of databases.
            These names have been added to the scope of Coq,
            and can hence directly be used with [auto].
*)
Local Ltac2 load_db_of_label (label: WaterproofDatabase) :=
    match label with
    | WaterproofDBAlgebra =>            (@waterproof_algebra)::[]
    | WaterproofDBMultiplication =>     (@eq_mult)::(@eq_opp)::[]
    | WaterproofDBPlusMinus =>          (@eq_plus)::(@eq_minus)::[]
    | WaterproofDBZeroOne =>            (@eq_zero)::(@eq_one)::(@eq_opp)::[]
    | WaterproofDBSquareRoot =>         (@eq_sqr)::[]
    | WaterproofDBExponential =>        (@eq_exp)::[]
    | WaterproofDBAbsoluteValue =>      (@eq_abs)::[]
    | WaterproofDBRealsAndIntegers =>   (@zarith)::(@waterproof_integers)::(@arith)::(@real)::(@reals)::[]
    | WaterproofDBSets =>               (@sets)::[]
    | WaterproofDBSubsets =>            (@subsets)::[]
    | WaterproofDBAdditional =>         (@additional)::[]
    | WaterproofDBReals =>              (@real)::(@reals)::[]
    | WaterproofDBClassicalLogic =>     (@classical_logic)::[]
    | WaterproofDBConstructiveLogic =>  (@constructive_logic)::(@classical_logic)::[]
    | WaterproofDBIntegers =>           (@zarith)::(@waterproof_integers)::(@arith)::[]
    | WaterproofDBIntuition =>          (@intuition)::[]
    | WaterproofDBFirstorder =>         (@firstorder)::[]
    (* Databases for manipulating negations. *)
    | WaterproofNegationDBIntegers =>   (@negation_int)::(@negation_nat)::(@nocore)::[]
    | WaterproofNegationDBReals =>      (@negation_reals)::(@nocore)::[]
    | WaterproofNegationDBRealsAndIntegers => (@negation_reals)::(@negation_int)::(@negation_nat)::(@nocore)::[]
    (* Databases for decidablity. *)
    | WaterproofDecidabilityDBReals =>  (@decidability_reals)::(@nocore)::[]
    | WaterproofDecidabilityDBNat   =>  (@decidability_nat)::(@nocore)::[]
    | _ => Aux.cannot_happen ""
    end.

(* Subroutine of [load_databases] *)
Local Ltac2 rec load_databases_rec 
    (db_label_list: WaterproofDatabase list)
    (db_as_ident_list : ident list) :=
    match db_label_list with
    | label::remaining_labels => 
        let dbs_to_add := load_db_of_label label in
        let updated_ident_list := List.append dbs_to_add db_as_ident_list in
        load_databases_rec remaining_labels updated_ident_list
    | [] => db_as_ident_list
    end.

(** * load_databases
    Maps a label specifying a database
    to a list of [ident]s that can actually be used to access the database.

    Arguments:
        - [db_label_list: WaterproofDatabase list], 
            list of labels.
            Each label specifies the list of database
            [ident]s (names) to load.
            Each label generally corresponds to a set of databases
            that are practically always used together.

    Returns:
        - [ident list], list of names of databases corresponding to the labels.
            For each label, contains the databases it maps to.
            See the local function [load_db_of_label] 
            for the meaning of the labels.
            These names have been added to the scope of Coq,
            and can hence directly be used with [auto].
            Contains the database [core], unless the database [nocore] is specified.
*)
Ltac2 load_databases (db_label_list: WaterproofDatabase list) := 
    load_databases_rec db_label_list [].

