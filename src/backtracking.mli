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
type trace = {
  log: bool; (** Are tried hints logged ? *)
  current_depth: int; (** The current depth of the search *)
  trace: trace_atom list ref (** The full trace of tried hints *)
}

(**
  Increases the debug depth by 1
*)
val incr_trace_depth : trace -> trace

(**
  Returns a [trace] value corresponding to [no trace recording]
*)
val no_trace : unit -> trace

(**
  Creates a [trace] value given a boolean indicating if tried hints are printed
*)
val new_trace : bool -> trace

(**
  Prints the complete info trace
*)
val pr_trace : Environ.env -> Evd.evar_map -> trace -> unit

(**
  Returns the trace atoms that have been actually applied during [wauto]

  It is supposed here that the given [trace] has not been modified since the end of [wauto] and that [wauto] is successful, i.e it succeed to solve the goal
*)
val keep_applied :
  trace_atom list -> (int * Pp.t * Pp.t) list
