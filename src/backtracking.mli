(**
  Trace atome type

  Can be read as `(is_success, depth, current_proof_state`, print_function_option, hint_name, hint_db_source)`
*)
type trace_atom = bool * int * Pp.t * Pp.t

(**
  Debug type
*)
type trace = {
  log : bool;
  current_depth : int;
  trace : trace_atom list;
}

(**
  Exception raised if no proof of the goal is found
*)
exception SearchBound of trace

(**
  Increases the debug depth by 1
*)
val incr_trace_depth : trace -> trace

(**
  [trace] value corresponding to "no trace recording"
*)
val no_trace : trace

(**
  Creates a [trace] value given a boolean indicating if tried hints are printed
*)
val new_trace : bool -> trace

(**
  Creates a trace containing only one atom 
*)
val singleton_trace : bool -> Pp.t -> Pp.t -> trace

(**
  Marks all the trace atoms contained in the given [trace] as unsuccessful
*)
val failed : trace -> trace

(**
  Concatenates the two given traces
*)
val merge_traces : trace -> trace -> trace

(**
  Prints an info atom, i.e an element of the info trace
*)
val pr_trace_atom : trace_atom -> Pp.t

(**
  Prints the complete info trace
*)
val pr_trace : trace -> unit

(**
  Returns the trace atoms that have been actually applied during a [trace tactic] (like {! Wauto.wauto})

  It is supposed here that the given [trace] has not been modified after getting it from the [trace tactic].
*)
val keep_applied : trace -> trace
