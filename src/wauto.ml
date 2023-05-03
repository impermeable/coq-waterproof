open Auto
open Hints
open Names
open Proofview.Notations
open Pp
open Tactics
open Termops
open Unification
open Util

open Backtracking

(* All the definitions below come from coq-core hidden library (i.e not visible in the API) *)

exception SearchBound

let auto_core_unif_flags_of st1 st2 = {
  modulo_conv_on_closed_terms = Some st1;
  use_metas_eagerly_in_conv_on_closed_terms = true;
  use_evars_eagerly_in_conv_on_closed_terms = false;
  modulo_delta = st2;
  modulo_delta_types = TransparentState.full;
  check_applied_meta_types = false;
  use_pattern_unification = false;
  use_meta_bound_pattern_unification = true;
  allowed_evars = Evarsolve.AllowedEvars.all;
  restrict_conv_on_strict_subterms = false;
  modulo_betaiota = false;
  modulo_eta = true;
}

let auto_unif_flags_of st1 st2 =
  let flags = auto_core_unif_flags_of st1 st2 in {
  core_unify_flags = flags;
  merge_unify_flags = flags;
  subterm_unify_flags = { flags with modulo_delta = TransparentState.empty };
  allow_K_in_toplevel_higher_order_unification = false;
  resolve_evars = true
}

let auto_unif_flags =
  auto_unif_flags_of TransparentState.full TransparentState.empty

let unify_resolve_nodelta h = Hints.hint_res_pf ~with_evars:true ~flags:auto_unif_flags h

let exact h =
  Proofview.Goal.enter begin fun gl ->
    let env = Proofview.Goal.env gl in
    let sigma = Proofview.Goal.sigma gl in
    let sigma, c = Hints.fresh_hint env sigma h in
    let sigma, t = Typing.type_of env sigma c in
    let concl = Proofview.Goal.concl gl in
    if occur_existential sigma t || occur_existential sigma concl then
      let sigma = Evd.clear_metas sigma in
      try
        let sigma = Unification.w_unify env sigma CONV ~flags:auto_unif_flags concl t in
        Proofview.Unsafe.tclEVARSADVANCE sigma <*>
        exact_no_check c
      with e when CErrors.noncritical e -> Proofview.tclZERO e
    else Proofview.Unsafe.tclEVARS sigma <*> exact_check c
  end

let exists_evaluable_reference (env: Environ.env) (evaluable_ref: Tacred.evaluable_global_reference) = match evaluable_ref with
  | Tacred.EvalConstRef _ -> true
  | Tacred.EvalVarRef v -> try ignore(Environ.lookup_named v env); true with Not_found -> false

(* All the definitions below are inspired by the coq-core hidden library (i.e not visible in the API) but modified for Waterproof *)

(**
  Prints "idtac" if the [log] field is [true]
*)
let pr_info_nop (trace: trace) = if trace.log then Feedback.msg_notice (str "idtac.") else ()

(** 
  Prints a debug header if [log] is [true]
*)
let pr_dbg_header (trace: trace) = if trace.log then Feedback.msg_notice (str "(* info wauto: *)") else ()

(**
  Tries the given tactic and calls an info printer if it fails
*)
let tcl_try_dbg (trace: trace) (debug_header_printer : trace -> unit) (tac: unit Proofview.tactic): unit Proofview.tactic =
  let delay f = Proofview.tclUNIT () >>= fun () -> f () in
  let tac =
    delay (fun () -> debug_header_printer trace; tac) >>= fun () ->
      Proofview.tclENV >>= fun env ->
      Proofview.tclEVARMAP >>= fun sigma ->
        pr_trace env sigma trace;
      Proofview.tclUNIT () in
  let after = delay (fun () -> pr_info_nop trace; Proofview.tclUNIT ()) in
  Tacticals.tclORELSE0 tac after

(**
  Creates a function that takes a hint database and returns a hint list
*)
let hintmap_of (env: Environ.env) (sigma: Evd.evar_map) (secvars: Id.Pred.t) (concl: Evd.econstr): hint_db -> FullHint.t list =
  let hdc = try Some (decompose_app_bound sigma concl) with Bound -> None in
  match hdc with
  | None -> Hint_db.map_none ~secvars
  | Some hdc ->
      if occur_existential sigma concl then (fun db -> 
        match Hint_db.map_eauto env sigma ~secvars hdc concl db with
          | ModeMatch (_, l) -> l
          | ModeMismatch -> []
      )
      else Hint_db.map_auto env sigma ~secvars hdc concl

(**
  Returns a logged [intro] tactic
*)
let dbg_intro (trace: trace): unit Proofview.tactic = Proofutils.tclLOG trace (fun _ _ -> (str "intro", str "")) intro

(**
  Returns a logged [assumption] tactic
*)
let dbg_assumption (trace: trace): unit Proofview.tactic = Proofutils.tclLOG trace (fun _ _ -> (str "assumption", str "")) assumption

(**
  Returns a tactic that apply intro then try to solve the goal
*)
let intro_register (trace: trace) (kont: hint_db -> unit Proofview.tactic) (db: hint_db): unit Proofview.tactic =
  Proofview.tclTHEN (dbg_intro trace) @@
    Proofview.Goal.enter begin fun gl ->
      let extend_local_db decl db =
        let env = Proofview.Goal.env gl in
        let sigma = Proofview.Goal.sigma gl in
        push_resolve_hyp env sigma (Context.Named.Declaration.get_id decl) db
      in
      Tacticals.onLastDecl (fun decl -> kont (extend_local_db decl db))
    end

let rec trivial_fail_db (trace: trace) (db_list: hint_db list) (local_db: hint_db): unit Proofview.tactic =
  Proofview.tclINDEPENDENT @@
    Tacticals.tclORELSE0 (dbg_assumption trace) @@
    Tacticals.tclORELSE0 (intro_register trace (trivial_fail_db trace db_list) local_db) @@
    Proofview.Goal.enter begin fun gl ->
      let env = Proofview.Goal.env gl in
      let sigma = Proofview.Goal.sigma gl in
      let concl = Proofview.Goal.concl gl in
      let secvars = compute_secvars gl in
      let hintmap = hintmap_of env sigma secvars concl in
      let hinttac = tac_of_hint trace db_list local_db concl in
      (local_db::db_list)
      |> List.map_append (fun db -> try hintmap db with Not_found -> [])
      |> List.filter_map begin fun h ->
           if Int.equal (FullHint.priority h) 0 then
             Some (Tacticals.tclCOMPLETE (hinttac h))
           else None
         end
      |> Tacticals.tclFIRST
    end

(**
  Returns a function that converts hints into tactics
*)
and tac_of_hint (trace: trace) (db_list: hint_db list) (local_db: hint_db) (concl: Evd.econstr): FullHint.t -> unit Proofview.tactic =
  let tactic = function
    | Res_pf h -> unify_resolve_nodelta h
    | ERes_pf _ -> Proofview.Goal.enter (fun gl ->
        let info = Exninfo.reify () in
        Tacticals.tclZEROMSG ~info (str "eres_pf"))
    | Give_exact h  -> exact h
    | Res_pf_THEN_trivial_fail h ->
      Tacticals.tclTHEN
        (unify_resolve_nodelta h)
        (* With "(debug) trivial", we shouldn't end here, and
           with "debug auto" we don't display the details of inner trivial *)
        (trivial_fail_db (no_trace ()) db_list local_db)
    | Unfold_nth c ->
      Proofview.Goal.enter begin fun gl ->
       if exists_evaluable_reference (Proofview.Goal.env gl) c then
         Tacticals.tclPROGRESS (reduce (Genredexpr.Unfold [Locus.AllOccurrences,c]) Locusops.onConcl)
       else
         let info = Exninfo.reify () in
         Tacticals.tclFAIL ~info (str"Unbound reference")
       end
    | Extern (p, tacast) ->
      conclPattern concl p tacast
  in
  let pr_hint (h: FullHint.t) (env: Environ.env) (sigma: Evd.evar_map): t * t =
    let origin = match FullHint.database h with
    | None -> mt ()
    | Some n -> str n
    in
    (Proofutils.pr_hint env sigma h, origin)
  in
  fun h -> Proofutils.tclLOG trace (pr_hint h) (FullHint.run h tactic)

(**
  Searches a sequence of at most [n] tactics within [db_list] and [lems] that solves the goal

  The goal cannot contain evars
*)
let search (trace: trace) (n: int) (db_list: hint_db list) (lems: Tactypes.delayed_open_constr list): unit Proofview.tactic =
  let make_local_db (gl: Proofview.Goal.t): hint_db =
    let env = Proofview.Goal.env gl in
    let sigma = Proofview.Goal.sigma gl in
    make_local_hint_db env sigma false lems
  in
  let rec search trace n local_db =
    if Int.equal n 0 then
      let info = Exninfo.reify () in
      Proofview.tclZERO ~info SearchBound
    else
      begin
        Tacticals.tclORELSE0 (dbg_assumption trace) @@
        Tacticals.tclORELSE0 (intro_register trace (search trace n) local_db) @@
        Proofview.Goal.enter begin fun gl ->
          let env = Proofview.Goal.env gl in
          let sigma = Proofview.Goal.sigma gl in
          let concl = Proofview.Goal.concl gl in
          let hyps = Proofview.Goal.hyps gl in
          let new_trace = incr_trace_depth trace in
          let secvars = compute_secvars gl in
          let hintmap = hintmap_of env sigma secvars  concl in
          let hinttac = tac_of_hint trace db_list local_db concl in
          (local_db::db_list)
            |> List.map_append (fun db -> try hintmap db with Not_found -> [])
            |> List.map 
              begin fun h ->
                Proofview.tclTHEN (hinttac h) @@
                  Proofview.Goal.enter 
                    begin fun gl ->
                      let hyps' = Proofview.Goal.hyps gl in
                      let local_db' =
                        if hyps' == hyps then local_db else make_local_db gl
                      in
                      search new_trace (n-1) local_db'
                    end
              end
            |> Tacticals.tclFIRST
        end
      end
  in
  Proofview.Goal.enter begin fun gl ->
    let local_db = make_local_db gl in
    search trace n local_db
  end

(** 
  Generates the [wauto] function
*)
let gen_wauto (trace: trace) ?(n: int = 5) (lems: Tactypes.delayed_open_constr list) (dbnames: hint_db_name list option) =
  Hints.wrap_hint_warning @@
    Proofview.Goal.enter begin fun gl ->
    let db_list =
      match dbnames with
      | Some dbnames -> make_db_list dbnames
      | None -> current_pure_db ()
    in
    wrap_hint_warning @@ tcl_try_dbg trace pr_dbg_header @@ search trace n db_list lems
  end

(**
  Waterproof auto

  This function is a rewrite around coq-core.Auto.auto with the same arguments to be able to retrieve which tactics have been used in case of success.

  The given [debug] will be updated with the trace at the end of the execution (consider using).
*)
let wauto (trace: trace) (n: int) (lems: Tactypes.delayed_open_constr list) (dbnames: hint_db_name list): unit Proofview.tactic = 
  gen_wauto trace ~n lems (Some dbnames)