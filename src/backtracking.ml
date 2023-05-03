open Pp

(**
  Trace atome type

  Can be read as `(is_success, depth, current_proof_state`, print_function_option, hint_name, hint_db_source)`
*)
type trace_atom = bool * int * t * t

(**
  Debug type
*)
type trace = {
  log: bool; (** Are tried hints printed ? *)
  current_depth: int; (** The current depth of the search *)
  trace: trace_atom list ref (** The full trace of tried hints *)
}

(**
  Increases the debug depth by 1
*)
let incr_trace_depth (trace: trace): trace = {log = trace.log; current_depth = trace.current_depth + 1; trace = trace.trace}

(**
  Returns a [trace] value corresponding to [no trace recording]
*)
let no_trace (): trace = {log = false; current_depth = 0; trace = ref []}

(**
  Creates a [trace] value given a boolean indicating if tried hints are printed
*)
let new_trace (log: bool): trace = {log = log; current_depth = 0; trace = ref []}

(**
  Cleans up the trace with a higher depth than the given [depth]
*)
let rec cleanup_info_trace (acc: trace_atom list) (trace: trace_atom list): trace_atom list =
  match trace with
    | [] -> acc
    | (is_success, d, hint, src) :: l -> cleanup_info_trace ((is_success, d, hint, src)::acc) l

(**
  Prints an info atom, i.e an element of the info trace
*)
let pr_trace_atom (env: Environ.env) (sigma: Evd.evar_map) ((is_success, d, hint, src): trace_atom): t =
  str (String.make d ' ') ++ str (if is_success then "✓" else "×") ++ spc () ++ hint ++ str " in (" ++ src ++ str ")."

(**
  Prints the complete info trace
*)
let pr_trace (env: Environ.env) (sigma: Evd.evar_map) (trace: trace): unit = match trace with
  | {log = true; trace = {contents=atom::l}; _} ->
    Feedback.msg_notice (prlist_with_sep fnl (pr_trace_atom env sigma) (cleanup_info_trace [atom] l))
  | _ -> ()

(**
  Returns the trace atoms that have been actually applied during [wauto] under the form `(depth, hint_name, hint_database_source)`

  It is supposed here that the given [trace] has not been modified since the end of [wauto]
*)
let keep_applied (trace: trace_atom list): (int * t * t) list = 
  List.rev @@ 
  List.filter_map (fun (is_success, depth, hint, src) ->
    match is_success with
      | true -> Some (depth, hint, src)
      | false -> None
  ) trace