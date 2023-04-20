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

let compute_secvars (gl: Proofview.Goal.t): Id.Pred.t =
  let hyps = Proofview.Goal.hyps gl in
  secvars_of_hyps hyps

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

let unify_resolve_nodelta h = Hints.hint_res_pf ~flags:auto_unif_flags h

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
        let sigma = Unification.w_unify env sigma Reduction.CONV ~flags:auto_unif_flags concl t in
        Proofview.Unsafe.tclEVARSADVANCE sigma <*>
        exact_no_check c
      with e when CErrors.noncritical e -> Proofview.tclZERO e
    else Proofview.Unsafe.tclEVARS sigma <*> exact_check c
  end

let conclPattern concl pat tac =
  let constr_bindings env sigma =
    match pat with
    | None -> Proofview.tclUNIT Id.Map.empty
    | Some pat ->
        try
          Proofview.tclUNIT (Constr_matching.matches env sigma pat concl)
        with Constr_matching.PatternMatchingFailure as exn ->
          let _, info = Exninfo.capture exn in
          Tacticals.tclZEROMSG ~info (str "pattern-matching failed")
  in
  Proofview.Goal.enter begin fun gl ->
     let env = Proofview.Goal.env gl in
     let sigma = Proofview.Goal.sigma gl in
     constr_bindings env sigma >>= fun constr_bindings ->
     Proofview.tclProofInfo [@ocaml.warning "-3"] >>= fun (_name, poly) ->
     let open Genarg in
     let open Geninterp in
     let inj c = match val_tag (topwit Stdarg.wit_constr) with
     | Val.Base tag -> Val.Dyn (tag, c)
     | _ -> assert false
     in
     let fold id c accu = Id.Map.add id (inj c) accu in
     let lfun = Id.Map.fold fold constr_bindings Id.Map.empty in
     let ist = { lfun
               ; poly
               ; extra = TacStore.empty } in
     match tac with
     | GenArg (Glbwit wit, tac) ->
      Ftactic.run (Geninterp.interp wit ist tac) (fun _ -> Proofview.tclUNIT ())
  end

let exists_evaluable_reference (env: Environ.env) (evaluable_ref: Tacred.evaluable_global_reference) = match evaluable_ref with
  | Tacred.EvalConstRef _ -> true
  | Tacred.EvalVarRef v -> try ignore(Environ.lookup_named v env); true with Not_found -> false

(* All the definitions below are inspired by the coq-core hidden library (i.e not visible in the API) but slightly modified for Waterproof *)

type debug = Hints.debug * int * (int * (Environ.env -> Evd.evar_map -> t) option) list ref

(**
  Returns a `debug` value corresponding to `no debug`
*)
let no_debug (): debug = (Off, 0, ref [])

(**
  Creates a `debug` value from a `Hints.debug` value
*)
let new_debug (debug: Hints.debug) = (debug, 0, ref [])

(**
  Increases the debug depth by 1
*)
let incr_debug_depth ((dbg, depth, trace): debug): debug = (dbg, depth + 1, trace)

(**
  Updates the given debug and print informations according to the field `Hints.debug`
*)
let tclLOG ((dbg, depth, trace): debug) (pp: Environ.env -> Evd.evar_map -> t) (tac: 'a Proofview.tactic): 'a Proofview.tactic =
  match dbg with
    | Off -> tac
    | Info ->
      Proofview.(tclIFCATCH (
        tac >>= fun v ->
          trace := (depth, Some pp) :: !trace;
          tclUNIT v
          ) Proofview.tclUNIT
          (fun (exn, info) ->
            trace := (depth, None) :: !trace;
            tclZERO ~info exn))
    | Debug ->
      let s = String.make (depth+1) '*' in
      Proofview.(tclIFCATCH (
          tac >>= fun v ->
          tclENV >>= fun env ->
          tclEVARMAP >>= fun sigma ->
          Feedback.msg_notice (str s ++ spc () ++ pp env sigma ++ str ". (*success*)");
          tclUNIT v
        ) tclUNIT
          (fun (exn, info) ->
              tclENV >>= fun env ->
              tclEVARMAP >>= fun sigma ->
              Feedback.msg_notice (str s ++ spc () ++ pp env sigma ++ str ". (*fail*)");
              tclZERO ~info exn))

(**
  Cleans up the trace with a higher depth than the given `depth`
*)
let rec cleanup_info_trace (depth: int) (acc: (int * (Environ.env -> Evd.evar_map -> t)) list): (int * (Environ.env -> Evd.evar_map -> t) option) list -> (int * (Environ.env -> Evd.evar_map -> t)) list = function
  | [] -> acc
  | (d, Some pp) :: l -> cleanup_info_trace d ((d,pp)::acc) l
  | l -> cleanup_info_trace depth acc (erase_subtree depth l)
  
(**
  Erases the trace with a higher depth that the given `depth`
*)
and erase_subtree (depth: int): (int * (Environ.env -> Evd.evar_map -> t) option) list -> (int * (Environ.env -> Evd.evar_map -> t) option) list = function
  | [] -> []
  | (d, _) :: l -> if Int.equal d depth then l else erase_subtree depth l


(**
  Prints an info atom, i.e an element of the info trace
*)
let pr_info_atom (env: Environ.env) (sigma: Evd.evar_map) ((d, pp): int * (Environ.env -> Evd.evar_map -> t)): t =
  str (String.make d ' ') ++ pp env sigma ++ str "."

(**
  Prints the complete info trace
*)
let pr_info_trace (env: Environ.env) (sigma: Evd.evar_map) (d: debug) = match d with
  | (Info, _, {contents=(d,Some pp)::l}) ->
    Feedback.msg_notice (prlist_with_sep fnl (pr_info_atom env sigma) (cleanup_info_trace d [(d,pp)] l))
  | _ -> ()

(**
  Prints "idtac" if the `Hints.debug` level is `Info`
*)
let pr_info_nop (d: debug) = match d with
  | (Info, _, _) -> Feedback.msg_notice (str "idtac.")
  | _ -> ()

(** 
  Prints a debug header according to the `Hints.debug` level
*)
let pr_dbg_header = function
  | (Off, _, _) -> ()
  | (Info, _, _) -> Feedback.msg_notice (str "(* info auto: *)")
  | (Debug, _, _) -> Feedback.msg_notice (str "(* debug auto: *)")

(**
  Tries the given tactic and print an "idtac" if case of fail
*)
let tclTRY_dbg (d: debug) (tac: unit Proofview.tactic): unit Proofview.tactic =
  let delay f = Proofview.tclUNIT () >>= fun () -> f () in
  let tac =
    delay (fun () -> pr_dbg_header d; tac) >>= fun () ->
      Proofview.tclENV >>= fun env ->
      Proofview.tclEVARMAP >>= fun sigma ->
      pr_info_trace env sigma d;
      Proofview.tclUNIT () in
  let after = delay (fun () -> pr_info_nop d; Proofview.tclUNIT ()) in
  Tacticals.tclORELSE0 tac after

(**
  Creates a function that takes a hint database and returns a hint list
*)
let hintmap_of (env: Environ.env) (sigma: Evd.evar_map) (secvars: Id.Pred.t) (hdc: (GlobRef.t * Evd.econstr array) option) (concl: Evd.econstr): hint_db -> FullHint.t list =
  match hdc with
  | None -> Hint_db.map_none ~secvars
  | Some hdc ->
      if occur_existential sigma concl then
        (fun db -> match Hint_db.map_eauto env sigma ~secvars hdc concl db with
                   | ModeMatch (_, l) -> l
                   | ModeMismatch -> [])
      else Hint_db.map_auto env sigma ~secvars hdc concl

(* Returns a logged `intro` tactic *)
let dbg_intro (dbg: debug): unit Proofview.tactic = tclLOG dbg (fun _ _ -> str "intro") intro

(* Returns a logged `assumption` tactic *)
let dbg_assumption (dbg: debug): unit Proofview.tactic = tclLOG dbg (fun _ _ -> str "assumption") assumption

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
      let hdc = try Some (decompose_app_bound sigma concl) with Bound -> None in
      let hintmap = hintmap_of env sigma secvars hdc concl in
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
  let pr_hint h env sigma =
    let origin = match FullHint.database h with
    | None -> mt ()
    | Some n -> str " (in " ++ str n ++ str ")"
    in
    FullHint.print env sigma h ++ origin
  in
  fun h -> tclLOG dbg (pr_hint h) (FullHint.run h tactic)

(* Searches a sequence of at most `n` tactics within `db_list` and `lems` that solves the goal *)
let search (d: debug) (n: int) (db_list: hint_db list) (lems: Tactypes.delayed_open_constr list): unit Proofview.tactic =
  let make_local_db gl =
    let env = Proofview.Goal.env gl in
    let sigma = Proofview.Goal.sigma gl in
    make_local_hint_db env sigma false lems
  in
  let rec search d n local_db =
    if Int.equal n 0 then
      let info = Exninfo.reify () in
      Proofview.tclZERO ~info SearchBound
    else
      begin
        (* Put mutable variable here to catch the value of the applied tactic *)
        Tacticals.tclORELSE0 (dbg_assumption d) @@
        Tacticals.tclORELSE0 (intro_register d (search d n) local_db) @@
        Proofview.Goal.enter begin fun gl ->
          let env = Proofview.Goal.env gl in
          let sigma = Proofview.Goal.sigma gl in
          let concl = Proofview.Goal.concl gl in
          let hyps = Proofview.Goal.hyps gl in
          let d' = incr_debug_depth d in
          let secvars = compute_secvars gl in
          let hdc = try Some (decompose_app_bound sigma concl) with Bound -> None in
          let hintmap = hintmap_of env sigma secvars hdc concl in
          let hinttac = tac_of_hint d db_list local_db concl in
          (local_db::db_list)
          |> List.map_append (fun db -> try hintmap db with Not_found -> [])
          |> List.map begin fun h ->
               Proofview.tclTHEN (hinttac h) @@
                 Proofview.Goal.enter begin fun gl ->
                   let hyps' = Proofview.Goal.hyps gl in
                   let local_db' =
                     (* update local_db if local hypotheses have changed *)
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
    search d n (make_local_db gl)
  end

(** 
  Generates the `wauto` function
*)
let gen_wauto (debug: debug) ?(n: int = 5) (lems: Tactypes.delayed_open_constr list) (dbnames: hint_db_name list option) =
  Hints.wrap_hint_warning @@
    Proofview.Goal.enter begin fun gl ->
    let db_list =
      match dbnames with
      | Some dbnames -> make_db_list dbnames
      | None -> current_pure_db ()
    in
    tclTRY_dbg debug (search debug n db_list lems)
  end

(**
  Waterproof auto

  This function is a rewrite around coq-core.Auto.auto to be able to retrieve which tactics have been used in case of success
*)
let wauto (debug: debug) (n: int) (lems: Tactypes.delayed_open_constr list) (dbnames: hint_db_name list): unit Proofview.tactic = 
  gen_wauto debug ~n lems (Some dbnames)

(**
  Wrapper around `Proofview.tclTHEN` who actually execute the first tactic before the second 
*)
let tclRealThen (first: unit Proofview.tactic) (second: unit Proofview.tactic lazy_t): unit Proofview.tactic =
  Proofview.tclBIND first (fun () -> Proofview.tclTHEN first (Lazy.force second))

let test (id: Names.Id.t) : unit Proofview.tactic =
  Feedback.msg_notice (Ppconstr.pr_id id);
  let debug = new_debug Info in
  let tactic = wauto debug 5 [] ["core"] in
  let print = lazy (
    let (_, _, trace) = debug in
    Proofview.tclUNIT @@ List.iter (fun (depth, _) -> Feedback.msg_notice (Pp.int depth)) !trace
  ) in
  tclRealThen tactic print