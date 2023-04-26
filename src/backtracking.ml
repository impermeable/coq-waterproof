open Pp

open Wauto

(**
  Returns the trace atoms that have been actually applied during `wauto` under the form `(depth, hint_name, hint_database_source)`

  It is supposed here that the given `trace` has not been modified since the end of `wauto`
*)
let keep_applied (trace: trace_atom list): (int * t * t) list = 
  List.rev @@ 
  List.filter_map (fun (is_success, depth, _, hint, src) ->
    match is_success with
      | true -> Some (depth, hint, src)
      | false -> None
  ) trace