(**
  Exception raised if no proof of the goal is found
*)
exception SearchBound

(**
  Trace atome type

  Can be read as `(is_success, depth, print_function_option, hint_name, hint_db_source)`
*)
type trace_atom =
  bool
  * int
  * Pp.t
  * Pp.t

(**
  Debug type
*)
type debug = {
  log_level: Hints.debug; (** Log level ([Off], [Info] or [Debug]) *)
  current_depth: int; (** The current depth of the search *)
  trace: trace_atom list ref (** The full trace of tried hints *)
}

(**
  Creates a [debug] value from a [Hints.debug] value
*)
val new_debug : Hints.debug -> debug

(**
  Updates the given debug and print informations according to the field [Hints.debug]
*)
val tclLOG :
  debug ->
  (Environ.env -> Evd.evar_map -> Pp.t * Pp.t) ->
  'a Proofview.tactic ->
  'a Proofview.tactic

(**
  Prints a trace atom
*)
val pr_trace_atom :
  Environ.env ->
  Evd.evar_map ->
  trace_atom ->
  Pp.t

(**
  Prints the complete info trace
*)
val pr_trace :
  Environ.env -> Evd.evar_map -> debug -> unit

(**
  Prints "idtac" if the [Hints.debug] level is [Info]
*)
val pr_info_nop : debug -> unit

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
  Creates a function that takes a hint database and returns a hint list
*)
val hintmap_of :
  Environ.env ->
  Evd.evar_map ->
  Names.Id.Pred.t ->
  Evd.econstr ->
  (Hints.hint_db -> Hints.FullHint.t list)

(**
  Waterproof auto

  This function is a rewrite around coq-core.Auto.auto with the same arguments to be able to retrieve which tactics have been used in case of success.

  The given [debug] will be updated with the trace at the end of the execution (consider using).
*)
val wauto :
  debug ->
  int ->
  Tactypes.delayed_open_constr list ->
  string list ->
  unit Proofview.tactic
