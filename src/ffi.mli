(**
  Small wrapper around Ltac2/OCaml Foreign Function Interface (FFI)

  This allows Ltac2 to call OCaml-defined functions
*)

module Tac2ffi = Ltac2_plugin.Tac2ffi
module Tac2env = Ltac2_plugin.Tac2env
module Tac2expr = Ltac2_plugin.Tac2expr

(** Creates a name used to define the function interface *)
val pname : string -> Tac2expr.ml_tactic_name

(** Wrapper around {! Tac2env.define_primitive} to make easier the primitive definition *)
val define_primitive : string -> 'a Tac2ffi.arity -> 'a -> unit

(** 
  Defines a function of arity 0 (that only take a [unit] as an argument)

  This function will be callable in Ltac2 with [Ltac2 @ external <ltac2_name>: unit := "coq-waterproof" "<name>".]
*)
val define0 :
  string -> Tac2ffi.valexpr Proofview.tactic -> unit

(** 
  Defines a function of arity 1 (that only take one argument)

  This function will be callable in Ltac2 with [Ltac2 @ external <ltac2_name>: <type> -> unit := "coq-waterproof" "<name>".]
*)
val define1 :
  string ->
  'a Tac2ffi.repr ->
  ('a -> Tac2ffi.valexpr Proofview.tactic) ->
  unit

(** 
  Defines a function of arity 2 of the same way than {! define1}
*)
val define2 :
  string ->
  'a Tac2ffi.repr ->
  'b Tac2ffi.repr ->
  ('a -> 'b -> Tac2ffi.valexpr Proofview.tactic) ->
  unit

(** 
  Defines a function of arity 3 of the same way than {! define1}
*)
val define3 :
  string ->
  'a Tac2ffi.repr ->
  'b Tac2ffi.repr ->
  'c Tac2ffi.repr ->
  ('a -> 'b -> 'c -> Tac2ffi.valexpr Proofview.tactic) ->
  unit

(** 
  Defines a function of arity 4 of the same way than {! define1}
*)
val define4 :
  string ->
  'a Tac2ffi.repr ->
  'b Tac2ffi.repr ->
  'c Tac2ffi.repr ->
  'd Tac2ffi.repr ->
  ('a -> 'b -> 'c -> 'd -> Tac2ffi.valexpr Proofview.tactic) ->
  unit

(** 
  Defines a function of arity 5 of the same way than {! define1}
*)
val define5 :
  string ->
  'a Tac2ffi.repr ->
  'b Tac2ffi.repr ->
  'c Tac2ffi.repr ->
  'd Tac2ffi.repr ->
  'e Tac2ffi.repr ->
  ('a ->
  'b ->
  'c ->
  'd ->
  'e ->
  Tac2ffi.valexpr Proofview.tactic) ->
  unit

(**
  Utilitary function to cast OCaml types into Ltac2-compatibles types

  Comes from [coq/plugins/ltac2/tac2tactics.ml]
*)
val delayed_of_thunk :
  'a Tac2ffi.repr ->
  (unit, 'a) Tac2ffi.fun1 ->
  Environ.env ->
  Evd.evar_map ->
  Evd.evar_map * 'a
