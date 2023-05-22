open Hints
open Pp
open Proofview
open Proofview.Notations

open Backtracking

(**
  Returns the index of the first element [x] of [l] such that `f x` is [true]
*)
let find_first (f: 'a -> bool) (l: 'a list): int option =
  let rec aux (index: int) (p: 'a list): int option = match p with
    | [] -> None
    | x::q when f x -> Some index
    | _::q -> aux (index + 1) q
  in aux 0 l

(**
  Returns the index of the last element [x] of [l] such that `f x` is [true]
*)
let find_last (f: 'a -> bool) (l: 'a list): int option =
  let rec aux (current_index: int) (last_index: int option) (p: 'a list): int option =
    match p with
      | [] -> last_index
      | x::q ->
        aux (current_index + 1) (if f x then Some current_index else last_index) q
  in aux 0 None l

(**
  Returns the queue of the given list after the [n]th element included
*)
let rec tail_end (l: 'a list) (n: int): 'a list = match (l, n) with
  | (_, 0) -> l
  | ([], _) -> []
  | (_::p, _) -> tail_end p (n - 1)


(**
  Generic dictionnary taking strings as keys
*)
module StringMap = Map.Make(String)

(**
  Wrapper around [Proofview.tclTHEN] who actually execute the first tactic before the second
*)
let tclRealThen (first: unit tactic) (second: 'a tactic lazy_t): 'a tactic =
  tclBIND first (fun () -> tclTHEN (tclUNIT ()) (Lazy.force second))

(**
  Rewrite of [Auto.tclLOG]

  Updates the trace contained in the given tactic.

  Fails if the hint's name is forbidden, or if the proof will be complete without using all must-use lemmas.

  Arguments:
  - [pp: Environ.env -> Evd.evar_map -> Pp.t * Pp.t]: function to obtain the printable version of [(hint_name, source_hint_database)]
  - [tac: trace tactic]: tactic that will be tried
  - [must_use: : Pp.t list]: list of tactics that must be used during the automation
  - [forbidden: : Pp.t list]: list of tactics that mustn't be used during the automation
*)
let tclLOG (pp: Environ.env -> Evd.evar_map -> Pp.t * Pp.t) (tac: trace tactic) (forbidden: Pp.t list): trace tactic =
  (
    tclIFCATCH (
      tac >>= fun trace ->
      tclENV >>= fun env ->
      tclEVARMAP >>= fun sigma ->
      let (hint, src) = pp env sigma in
      if List.mem hint forbidden
        then tclZERO ~info:(Exninfo.reify ()) (SearchBound trace)
        else tclUNIT { trace with trace = (true, trace.current_depth, hint, src)::trace.trace }
    ) tclUNIT (fun (exn, info) ->
        tclENV >>= fun env ->
        tclEVARMAP >>= fun sigma ->
        let (hint, src) = pp env sigma in
        let trace = begin match exn with
          | SearchBound trace ->  trace 
          | _ -> no_trace
        end in tclZERO ~info (SearchBound (merge_traces trace @@ singleton_trace false hint src))
    )
  )

(**
  Checks if every hint in [must_use] is contained in [tac] and returns an exception if not
*)
let trace_check_used (must_use: t list) (trace: trace): trace tactic =
  let used_lemmas = ref StringMap.empty in
  List.iter (fun name -> used_lemmas := StringMap.add (string_of_ppcmds name) false !used_lemmas) must_use;
  List.iter (fun (_, _, hint, _) -> used_lemmas := StringMap.update (string_of_ppcmds hint) (fun value -> match value with
    | None -> None
    | Some _ -> Some true
  ) !used_lemmas) trace.trace;
  let unused_lemmas = ref [] in
  if StringMap.exists (fun name is_used -> if (not is_used) then unused_lemmas := name::!unused_lemmas; not is_used) !used_lemmas
    then tclZERO ~info:(Exninfo.reify ()) (SearchBound (failed trace))
    else tclUNIT trace

(**
  Wrapper around {! Proofview.tclTHEN} with a merge of tactics' traces
*)
let tclTraceThen (tac1: trace tactic) (tac2: trace tactic): trace tactic =
  tac1 >>= fun trace1 ->
  tac2 >>= fun trace2 ->
  tclUNIT @@ merge_traces trace1 trace2

(**
  Merge a list of traces contained in a tactic into one trace

  Useful to combine with {! Proofview.tclINDEPENDENTL}
*)
let tclAggregateTraces (tac: trace list tactic): trace tactic =
  tac >>= fun traces ->
  tclUNIT @@ List.fold_left merge_traces no_trace traces

(**
  Wrapper around {! Proofview.Goal.enter} to allow [Backtracking.trace tactic] and not just [unit tactic]
*)
let trace_goal_enter (f: Goal.t -> trace tactic): trace tactic =
  let value = ref [] in
  tclRealThen
    begin
      Goal.enter @@ fun goal ->
        begin
          f goal >>= fun trace ->
          value := trace::!value;
          tclUNIT ()
        end
    end @@
    lazy (tclUNIT @@ List.fold_left merge_traces no_trace (List.rev !value))

(**
  Rewrite of {! Tacticals.tclORELSE0} to give the trace of the failed tactic instead of the exception
*)
let tclOrElse0 (tac1: trace tactic) (f: trace -> trace tactic): trace tactic =
  tclAggregateTraces @@ 
    begin
      tclINDEPENDENTL @@
      tclORELSE tac1 
        begin fun (e, info) -> match e with
          | SearchBound trace -> f trace
          | _ -> f no_trace
        end
    end

(**
  Wrapper around {! tclOrElse0} with merge of trace contained in the failed [trace tactic] into the second one
*)
let tclTraceOrElse (tac1: trace tactic) (tac2: trace tactic): trace tactic =
  tclOrElse0 tac1 @@ fun trace1 -> tac2 >>= fun trace2 -> tclUNIT @@ merge_traces (failed trace1) trace2

(**
  Rewrite of {! Tacticals.tclTraceFirst} with [trace tactic] with a merge of traces of failed tactics 
*)
let tclTraceFirst (tacs: trace tactic list): trace tactic = 
  let rec aux (tacs: trace tactic list) (failed_trace: trace): trace tactic = match tacs with
    | [] -> let info = Exninfo.reify () in tclZERO ~info (SearchBound failed_trace)
    | tac::rest -> 
      tclOrElse0 tac @@ fun trace1 ->
        aux rest { failed_trace with trace = List.append (failed trace1).trace failed_trace.trace  }
  in aux tacs no_trace

(**
  Rewrite of Coq's hint printer to keep only the necessary parts
*)
let pr_hint (env: Environ.env) (sigma: Evd.evar_map) (h: FullHint.t) = 
  let pr_hint_elt env sigma h = Printer.pr_econstr_env env sigma (snd @@ hint_as_term h) in
  match FullHint.repr h with
    | Res_pf c -> pr_hint_elt env sigma c
    | ERes_pf c -> pr_hint_elt env sigma c
    | Give_exact c -> pr_hint_elt env sigma c
    | Res_pf_THEN_trivial_fail c -> pr_hint_elt env sigma c
    | Unfold_nth c -> Printer.pr_evaluable_reference c
    | Extern (_, tac) -> Pputils.pr_glb_generic env sigma tac