Require Import Ltac2.Ltac2.

Require Import Waterproof.

Require Import Ltac2.Init.

Ltac2 Type database_type_ffi.

Ltac2 @ external database_type_positive: unit -> database_type_ffi := "coq-waterproof" "database_type_positive".
Ltac2 @ external database_type_negative: unit -> database_type_ffi := "coq-waterproof" "database_type_negative".
Ltac2 @ external database_type_decidability: unit -> database_type_ffi := "coq-waterproof" "database_type_decidability".
Ltac2 @ external database_type_shorten: unit -> database_type_ffi := "coq-waterproof" "database_type_shorten".

Ltac2 @ external waterprove_ffi: int -> bool -> (unit -> constr) list -> database_type_ffi -> unit := "coq-waterproof" "waterprove".

Ltac2 Type database_type := [ Positive | Negative | Decidability | Shorten ].

Ltac2 database_type_to_ffi (db_type: database_type): database_type_ffi :=
  match db_type with
    | Positive => database_type_positive ()
    | Negative => database_type_negative ()
    | Decidability => database_type_decidability ()
    | Shorten => database_type_shorten ()
  end.

Ltac2 waterprove (depth: int) (log: bool) (lems: (unit -> constr) list) (db_type: database_type): unit  :=
  waterprove_ffi depth log lems (database_type_to_ffi db_type).