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
  - a current depth of `depth`
  - a full `trace` of tried hints
  - the names of the given lemmas
*)
type debug = {log_level: Hints.debug; current_depth: int; trace: trace_atom list ref}

(**
  Creates a `debug` value from a `Hints.debug` value
*)
val new_debug : Hints.debug -> debug

val pr_trace_atom :
  Environ.env -> Evd.evar_map -> trace_atom -> Pp.t

(**
  Prints the complete info trace
*)
val pr_trace :
  Environ.env -> Evd.evar_map -> debug -> unit

(**
  Prints "idtac" if the `Hints.debug` level is `Info`
*)
val pr_info_nop : debug -> unit

(** 
  Prints a debug header according to the `Hints.debug` level
*)
val pr_dbg_header : debug -> unit

(**
  Cleans up the trace with a higher depth than the given `depth`
*)
val cleanup_info_trace :
  int -> trace_atom list -> trace_atom list -> trace_atom list

(**
  Tries the given tactic and calls an info printer if it fails
*)
val tclTRY_dbg :
  debug ->
  (debug -> unit) ->
  (Environ.env -> Evd.evar_map -> debug -> unit) ->
  (debug -> unit) ->
  unit Proofview.tactic ->
  unit Proofview.tactic

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