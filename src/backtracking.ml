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
      
      (* 
        Explaination of how it works : 
          * If `wauto` is successful, the current goal and all of the subgoals generated are proved.
          * The associated trace will look like (by considerating only the depth) [0, 0, ..., 1, ..., 2, ..., 1, ..., 2, ..., 3, ...] :
            which is important here is that the depth is not decreasing : it only starts at 0.
          * To retrieve which hints have been applied, it suffices to get the last trace atom of a same-depth sequence of atoms.
          * Do not forget that the trace is given in the reverse order due to its creation.
      *)

      (* Returns the first element successful with a different depth than the first *)
      let rec find_previous_step (depth: int) (remaining_trace: trace_atom list): (int * t * t) list =
        if depth = 0
          then []
          else
            
            let next_depth_index =
              match Proofutils.find_first (fun (is_success, dpt, _, _, _) -> is_success && dpt <> depth) remaining_trace with
                | None -> throw (FailedBacktracing "Inconsistent trace")
                | Some n -> n
            in let ((_, dpt, _, hint, src), remaining_tail) = match Proofutils.tail_end remaining_trace next_depth_index with 
              | [] -> failwith "unreachable"
              | head::tail -> (head, tail)
            
            in (dpt, hint, src)::find_previous_step dpt remaining_tail
      
      in List.rev @@ (depth, hint, src)::(find_previous_step depth remaining_trace)