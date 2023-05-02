open Auto
open Hints
open Names
open Proofview.Notations
open Pp
open Tactics
open Termops
open Unification
open Util

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
  Trace atome type

  Can be read as `(is_success, depth, current_proof_state`, print_function_option, hint_name, hint_db_source)`
*)
type trace_atom = bool * int * t * t

(**
  Debug type
*)
type debug = {
  log_level: Hints.debug; (** Log level ([Off], [Info] or [Debug]) *)
  current_depth: int; (** The current depth of the search *)
  trace: trace_atom list ref (** The full trace of tried hints *)
}

(**
  Returns a [debug] value corresponding to `no debug`
*)
let no_debug (): debug = {log_level = Off; current_depth = 0; trace = ref []}

(**
  Creates a [debug] value from a [Hints.debug] value
*)
let new_debug (debug: Hints.debug): debug = {log_level = debug; current_depth = 0; trace = ref []}

(**
  Increases the debug depth by 1
*)
let incr_debug_depth (dbg: debug): debug = {log_level = dbg.log_level; current_depth = dbg.current_depth + 1; trace = dbg.trace}

(**
  Updates the given debug and print informations according to the field [Hints.debug]
*)
let tclLOG (dbg: debug) (pp: Environ.env -> Evd.evar_map -> t * t) (tac: 'a Proofview.tactic): 'a Proofview.tactic =
  let s = String.make (dbg.current_depth + 1) '*' in
  Proofview.(
    tclIFCATCH (
      tac >>= fun v ->
      tclENV >>= fun env ->
      tclEVARMAP >>= fun sigma ->
      let (hint, src) = pp env sigma in
      dbg.trace := (true, dbg.current_depth, hint, src) :: !(dbg.trace);
      if dbg.log_level = Debug then Feedback.msg_notice (str s ++ spc () ++ hint ++ str " in(" ++ src ++ str "). (*success*)");
      tclUNIT v
    ) tclUNIT (fun (exn,info) ->
        tclENV >>= fun env ->
        tclEVARMAP >>= fun sigma ->
        match dbg.log_level with
          | Off -> tac
          | Info ->
            dbg.trace := (false, dbg.current_depth, str "", str "") :: !(dbg.trace);
            tclZERO ~info exn
          | Debug -> 
            let (hint, src) = pp env sigma in
            Feedback.msg_notice (str s ++ spc () ++ hint ++ str " in(" ++ src ++ str "). (*fail*)");
            tclZERO ~info exn
    )
  )

(**
  Cleans up the trace with a higher depth than the given [depth]
*)
let rec cleanup_info_trace (depth: int) (acc: trace_atom list) (trace: trace_atom list): trace_atom list =
  match trace with
    | [] -> acc
    | (is_success, d, hint, src) :: l -> cleanup_info_trace d ((is_success, d, hint, src)::acc) l

(**
  Prints an info atom, i.e an element of the info trace
*)
let pr_trace_atom (env: Environ.env) (sigma: Evd.evar_map) ((is_success, d, hint, src): trace_atom): t =
  str (String.make d ' ') ++ hint ++ str " in (" ++ src ++ str ")."

(**
  Prints the complete info trace
*)
let pr_trace (env: Environ.env) (sigma: Evd.evar_map) (dbg: debug) = match dbg with
  | {log_level = Info; trace = {contents=(is_success, d, hint, src)::l}; _} ->
    Feedback.msg_notice (prlist_with_sep fnl (pr_trace_atom env sigma) (cleanup_info_trace d [(is_success, d, hint, src)] l))
  | _ -> ()

(**
  Prints "idtac" if the [Hints.debug] level is [Info]
*)
let pr_info_nop (dbg: debug) = match dbg.log_level with
  | Info -> Feedback.msg_notice (str "idtac.")
  | _ -> ()

(** 
  Prints a debug header according to the [Hints.debug] level
*)
let pr_dbg_header (dbg: debug) = match dbg.log_level with
  | Off -> ()
  | Info -> Feedback.msg_notice (str "(* info wauto: *)")
  | Debug -> Feedback.msg_notice (str "(* debug wauto: *)")

(**
  Tries the given tactic and calls an info printer if it fails
*)
let tclTRY_dbg (d: debug) (debug_header_printer : debug -> unit) (info_trace_printer: Environ.env -> Evd.evar_map -> debug -> unit
) (info_nop_printer: debug -> unit) (tac: unit Proofview.tactic): unit Proofview.tactic =
  let delay f = Proofview.tclUNIT () >>= fun () -> f () in
  let tac =
    delay (fun () -> debug_header_printer d; tac) >>= fun () ->
      Proofview.tclENV >>= fun env ->
      Proofview.tclEVARMAP >>= fun sigma ->
        info_trace_printer env sigma d;
      Proofview.tclUNIT () in
  let after = delay (fun () -> info_nop_printer d; Proofview.tclUNIT ()) in
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
let dbg_intro (dbg: debug): unit Proofview.tactic = tclLOG dbg (fun _ _ -> (str "intro", str "")) intro

(**
  Returns a logged [assumption] tactic
*)
let dbg_assumption (dbg: debug): unit Proofview.tactic = tclLOG dbg (fun _ _ -> (str "assumption", str "")) assumption

(**
  Returns a tactic that apply intro then try to solve the goal
*)
let intro_register (dbg: debug) (kont: hint_db -> unit Proofview.tactic) (db: hint_db): unit Proofview.tactic =
  Proofview.tclTHEN (dbg_intro dbg) @@
    Proofview.Goal.enter begin fun gl ->
      let extend_local_db decl db =
        let env = Proofview.Goal.env gl in
        let sigma = Proofview.Goal.sigma gl in
        push_resolve_hyp env sigma (Context.Named.Declaration.get_id decl) db
      in
      Tacticals.onLastDecl (fun decl -> kont (extend_local_db decl db))
    end

let rec trivial_fail_db (dbg: debug) (db_list: hint_db list) (local_db: hint_db): unit Proofview.tactic =
  Proofview.tclINDEPENDENT @@
    Tacticals.tclORELSE0 (dbg_assumption dbg) @@
    Tacticals.tclORELSE0 (intro_register dbg (trivial_fail_db dbg db_list) local_db) @@
    Proofview.Goal.enter begin fun gl ->
      let env = Proofview.Goal.env gl in
      let sigma = Proofview.Goal.sigma gl in
      let concl = Proofview.Goal.concl gl in
      let secvars = compute_secvars gl in
      let hintmap = hintmap_of env sigma secvars concl in
      let hinttac = tac_of_hint dbg db_list local_db concl in
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
and tac_of_hint (dbg: debug) (db_list: hint_db list) (local_db: hint_db) (concl: Evd.econstr): FullHint.t -> unit Proofview.tactic =
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
        (trivial_fail_db (no_debug ()) db_list local_db)
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
  fun h -> tclLOG dbg (pr_hint h) (FullHint.run h tactic)

(**
  Searches a sequence of at most [n] tactics within [db_list] and [lems] that solves the goal

  The goal cannot contain evars
*)
let search (dbg: debug) (n: int) (db_list: hint_db list) (lems: Tactypes.delayed_open_constr list): unit Proofview.tactic =
  let make_local_db (gl: Proofview.Goal.t): hint_db =
    let env = Proofview.Goal.env gl in
    let sigma = Proofview.Goal.sigma gl in
    make_local_hint_db env sigma false lems
  in
  let rec search dbg n local_db =
    if Int.equal n 0 then
      let info = Exninfo.reify () in
      Proofview.tclZERO ~info SearchBound
    else
      begin
        Tacticals.tclORELSE0 (dbg_assumption dbg) @@
        Tacticals.tclORELSE0 (intro_register dbg (search dbg n) local_db) @@
        Proofview.Goal.enter begin fun gl ->
          let env = Proofview.Goal.env gl in
          let sigma = Proofview.Goal.sigma gl in
          let concl = Proofview.Goal.concl gl in
          let hyps = Proofview.Goal.hyps gl in
          let d' = incr_debug_depth dbg in
          let secvars = compute_secvars gl in
          let hintmap = hintmap_of env sigma secvars  concl in
          let hinttac = tac_of_hint dbg db_list local_db concl in
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
                      search d' (n-1) local_db'
                    end
              end
            |> Tacticals.tclFIRST
        end
      end
  in
  Proofview.Goal.enter begin fun gl ->
    let local_db = make_local_db gl in
    search dbg n local_db
  end

(** 
  Generates the [wauto] function
*)
let gen_wauto (debug: debug) ?(n: int = 5) (lems: Tactypes.delayed_open_constr list) (dbnames: hint_db_name list option) =
  Hints.wrap_hint_warning @@
    Proofview.Goal.enter begin fun gl ->
    let db_list =
      match dbnames with
      | Some dbnames -> make_db_list dbnames
      | None -> current_pure_db ()
    in
    wrap_hint_warning @@ tclTRY_dbg debug pr_dbg_header pr_trace pr_info_nop @@ search debug n db_list lems
  end

(**
  Waterproof auto

  This function is a rewrite around coq-core.Auto.auto with the same arguments to be able to retrieve which tactics have been used in case of success.

  The given [debug] will be updated with the trace at the end of the execution (consider using).
*)
let wauto (debug: debug) (n: int) (lems: Tactypes.delayed_open_constr list) (dbnames: hint_db_name list): unit Proofview.tactic = 
  gen_wauto debug ~n lems (Some dbnames)