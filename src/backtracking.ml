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
      
      (* Returns the last element of the consecutive sequence of same-depth atoms beginning at the first atom with a different depth *)
      let rec find_previous_step (depth: int) (remaining_trace: trace_atom list): (int * t * t) list =
        if depth = 0
          then []
          else
            let next_depth_index =
              match Proofutils.find_first (fun (is_success, dpt, _, _, _) -> is_success && dpt <> depth) remaining_trace with
                | None -> throw (FailedBacktracing "Inconsistent trace")
                | Some n -> n
            in let tail = Proofutils.tail_end remaining_trace next_depth_index in

            (* Returns the last atom of the **consecutive** sequence that have the same depth as the first element and the remaining sequence *)
            let find_last_atom_with_same_depth (trace_part: trace_atom list): (trace_atom * trace_atom list) =
              let rec aux (l: trace_atom list) (previous_atom: trace_atom): (trace_atom * trace_atom list) = 
                match trace_part with
                | [] -> (previous_atom, [])
                | x::p ->
                  let (_, previous_atom_depth, _, ph, _) = previous_atom in
                  let (_, x_depth, _, px, _) = x in
                  Feedback.msg_notice (ph ++ str "/" ++ px);
                  if x_depth = previous_atom_depth then aux p x else (previous_atom, p)
              in aux (List.tl trace_part) (List.hd trace_part)
            in failwith "TODO";
            
            let ((_, dpt, _, hint, src), remaining_tail) = find_last_atom_with_same_depth tail in
            (dpt, hint, src)::find_previous_step dpt remaining_tail
      
      in List.rev @@ (depth, hint, src)::(find_previous_step depth remaining_trace)