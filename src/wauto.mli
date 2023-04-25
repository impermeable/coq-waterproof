(**
  Trace atome type

  Can be read as `(is_success, depth, print_function_option, hint_name, hint_db_source)`
*)
type trace_atom =
  bool
  * int
  * (Environ.env -> Evd.evar_map -> Pp.t * Pp.t)
  * Pp.t
  * Pp.t

(**
  Debug type

  A debug value of `(debug_type, depth, trace, lemma_names)` corresponds to :
  - a debug level of `debug_type`
  - a maximal depth of `depth`
  - a full `trace` of tried hints
  - the names of the given lemmas
*)
type debug =
  Hints.debug * int * trace_atom list ref * Pp.t list ref

(**
  Creates a `debug` value from a `Hints.debug` value
*)
val new_debug : Hints.debug -> debug

(**
  Waterproof auto

  This function is a rewrite around coq-core.Auto.auto with the same arguments to be able to retrieve which tactics have been used in case of success.

  The given `debug` will be updated with the trace at the end of the execution (consider using).
*)
val wauto :
  debug ->
  int ->
  Tactypes.delayed_open_constr list ->
  string list ->
  unit Proofview.tactic
