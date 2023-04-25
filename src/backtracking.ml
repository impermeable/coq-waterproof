open Pp

open Exceptions
open Wauto

(**
  Returns the trace atoms that have been actually applied during `wauto` under the form `(depth, hint_name, hint_database_source)`

  It is supposed here that the given `trace` has not been modified since the end of `wauto`
*)
let keep_applied (trace: trace_atom list): (int * t * t) list =
  match trace with
    | [] -> []
    | (false, _, _, _, _)::_ -> [(0, str "idtac", str "")]
    | (true, depth, _, hint, src)::remaining_trace ->
      let rec find_previous_step (depth: int) (remaining_trace: trace_atom list): (int * t * t) list =
        if depth = 0
          then []
          else
            let next_depth_index = 
              match Proofutils.find_last (fun (is_success, dpt, _, _, _) -> is_success && dpt = depth - 1) remaining_trace with
                | None -> throw (FailedBacktracing "Inconsistent trace")
                | Some n -> n
            in let (_, _, _, hint, src) = List.nth remaining_trace next_depth_index in
            (depth - 1, hint, src)::find_previous_step (depth - 1) (Proofutils.tail_end remaining_trace (next_depth_index + 1))
      in List.rev @@ (depth, hint, src)::(find_previous_step depth remaining_trace)