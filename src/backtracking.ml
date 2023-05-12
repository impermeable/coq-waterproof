open Pp

(**
  Trace atome type

  Can be read as [(is_success, depth, print_function_option, hint_name, hint_db_source)]
*)
type trace_atom = bool * int * t * t

(**
  Debug type
*)
type trace = {
  log: bool; (** Are tried hints printed ? *)
  current_depth: int; (** The current depth of the search *)
  trace: trace_atom list (** The full trace of tried hints *)
}

(**
  Exception raised if no proof of the goal is found
*)
exception SearchBound of trace

(**
  Increases the debug depth by 1
*)
let incr_trace_depth (trace: trace): trace = {log = trace.log; current_depth = trace.current_depth + 1; trace = trace.trace}

(**
  [trace] value corresponding to "no trace recording"
*)
let no_trace: trace = {log = false; current_depth = 0; trace = []}

(**
  Creates a [trace] value given a boolean indicating if tried hints are printed
*)
let new_trace (log: bool): trace = {log = log; current_depth = 0; trace = []}

(**
  Creates a trace containing only one atom 
*)
let singleton_trace (is_success: bool) (hint_name: t) (src: t): trace =
  {
    log = false;
    current_depth = 0;
    trace = [(is_success, 0, hint_name, src)];
  }

(**
  Marks all the trace atoms contained in the given [trace] as unsuccessful
*)
let failed (trace: trace): trace =
  let rec aux (atoms: trace_atom list): trace_atom list = match atoms with
    | [] -> []
    | (_, depth, hint, src)::rest -> (false, depth, hint, src)::(aux rest)
  in { trace with trace = aux trace.trace }

(**
  Concatenates the two given traces
*)
let merge_traces (trace1: trace) (trace2: trace): trace =
  { trace1 with trace = List.append trace1.trace trace2.trace }

(**
  Prints an info atom, i.e an element of the info trace
*)
let pr_trace_atom ((is_success, d, hint, src): trace_atom): t =
  str (String.make d ' ') ++ str (if is_success then "✓" else "×") ++ spc () ++ hint ++ str " in (" ++ src ++ str ")."

(**
  Prints the complete info trace
*)
let pr_trace (trace: trace): unit =
  Feedback.msg_notice (str "Trace:");
  Feedback.msg_notice (prlist_with_sep fnl pr_trace_atom trace.trace)

(**
  Returns the trace atoms that have been actually applied during a [trace tactic] (like {! Wauto.wauto})

  It is supposed here that the given [trace] has not been modified after getting it from the [trace tactic].
*)
let keep_applied (trace: trace): trace = 
  { trace with trace = List.filter (fun (is_applied, _, _, _) -> is_applied) trace.trace }