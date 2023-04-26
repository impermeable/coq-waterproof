open Hints
open Proofview
open Pp

open Wauto

let esearch (d: debug) (n: int) (db_list: hint_db list) (lems: Tactypes.delayed_open_constr list): unit Proofview.tactic =
  tclUNIT ()

(* let esearch (d: debug) (n: int) (db_list: hint_db list) (lems: Tactypes.delayed_open_constr list): unit Proofview.tactic =
  Proofview.Goal.enter begin fun gl ->
  let local_db env sigma = make_local_hint_db env sigma ~ts:TransparentState.full true lems in
  let is_debug = match d with 
    | Debug -> true
    | _ -> false in
  let tac s = Search.search ~debug db_list lems s in
  let () = pr_dbg_header d in
  Proofview.tclORELSE
    begin
      let evk = Proofview.goal_with_state (Proofview.Goal.goal gl) (Proofview.Goal.state gl) in
      tac (make_initial_state evk d p local_db) >>= fun s ->
      let () = pr_info d s in
      let () = assert (List.is_empty s.tacres) in
      Proofview.Unsafe.tclSETGOALS []
    end
    begin function
    | (Search.SearchFailure, _) ->
      let () = pr_info_nop d in
      Proofview.tclUNIT ()
    | (e, info) -> Proofview.tclZERO ~info e
    end
  end *)

(** 
  Prints a debug header according to the `Hints.debug` level
*)
let pr_dbg_header (dbg: debug) = match dbg.log_level with
  | Off -> ()
  | Info -> Feedback.msg_notice (str "(* info weauto: *)")
  | Debug -> Feedback.msg_notice (str "(* debug weauto: *)")


(** 
  Generates the `weauto` function
*)
let gen_weauto (debug: debug) ?(n: int = 5) (lems: Tactypes.delayed_open_constr list) (dbnames: hint_db_name list option) =
  Hints.wrap_hint_warning @@
    Proofview.Goal.enter begin fun gl ->
    let db_list =
      match dbnames with
      | Some dbnames -> make_db_list dbnames
      | None -> current_pure_db ()
    in
    wrap_hint_warning @@ tclTRY_dbg debug pr_dbg_header pr_trace pr_info_nop (esearch debug n db_list lems)
  end

(**
  Waterproof eauto

  This function is a rewrite around coq-core.Eauto.eauto with the same arguments to be able to retrieve which tactics have been used in case of success.

  The given `debug` will be updated with the trace at the end of the execution (consider using).

  The code structure has been rearranged to match the one of `Wauto.wauto`.
*)
let weauto (debug: debug) (n: int) (lems: Tactypes.delayed_open_constr list) (dbnames: hint_db_name list): unit Proofview.tactic = 
  gen_weauto debug ~n lems (Some dbnames)