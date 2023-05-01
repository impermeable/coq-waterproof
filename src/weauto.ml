open Hints
open Pp

open Wauto

(** 
  Prints a debug header according to the `Hints.debug` level
*)
let pr_dbg_header (dbg: debug) = match dbg.log_level with
  | Off -> ()
  | Info -> Feedback.msg_notice (str "(* info weauto: *)")
  | Debug -> Feedback.msg_notice (str "(* debug weauto: *)")

let gen_weauto (debug: debug) ?(n: int = 5) (lems: Tactypes.delayed_open_constr list) (dbnames: hint_db_name list option) =
  Hints.wrap_hint_warning @@
    Proofview.Goal.enter begin fun gl ->
    let db_list =
      match dbnames with
      | Some dbnames -> make_db_list dbnames
      | None -> current_pure_db ()
    in
    wrap_hint_warning @@ tclTRY_dbg debug pr_dbg_header pr_trace pr_info_nop (search debug n db_list lems true)
  end

(**
  Waterproof eauto

  This function is a rewrite around coq-core.Eauto.eauto with the same arguments to be able to retrieve which tactics have been used in case of success.

  The given `debug` will be updated with the trace at the end of the execution (consider using).

  The code structure has been rearranged to match the one of `Wauto.wauto`.
*)
let weauto (debug: debug) (n: int) (lems: Tactypes.delayed_open_constr list) (dbnames: hint_db_name list): unit Proofview.tactic = 
  gen_weauto debug ~n lems (Some dbnames)