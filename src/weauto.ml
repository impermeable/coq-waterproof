open Auto
open Context.Named
open EConstr
open Genredexpr
open Hints
open Locus
open Locusops
open Names
open Pp
open Proofview
open Proofview.Notations
open Tactics
open Termops
open Util

open Backtracking
open Wauto

(* All the definitions below come from coq-core hidden library (i.e not visible in the API) *)

let eauto_unif_flags: Unification.unify_flags = auto_flags_of_state TransparentState.full

let e_give_exact ?(flags: Unification.unify_flags = eauto_unif_flags) (c: types): unit tactic =
  Proofview.Goal.enter begin fun gl ->
  let sigma, t1 = Tacmach.pf_type_of gl c in
  let t2 = Tacmach.pf_concl gl in
  if occur_existential sigma t1 || occur_existential sigma t2 then
    Tacticals.tclTHENLIST
      [Proofview.Unsafe.tclEVARS sigma;
       Clenv.unify ~flags t1;
       exact_no_check c]
  else exact_check c
  end

let e_assumption: unit tactic =
  Proofview.Goal.enter begin fun gl ->
    let hyps = Proofview.Goal.hyps gl in
    let sigma = Proofview.Goal.sigma gl in
    let concl = Tacmach.pf_concl gl in
    if List.is_empty hyps then
      Tacticals.tclZEROMSG (str "No applicable tactic.")
    else
      let not_ground = occur_existential sigma concl in
      let map decl =
        let id = Declaration.get_id decl in
        let t = Declaration.get_type decl in
        if not_ground || occur_existential sigma t then
          Clenv.unify ~flags:eauto_unif_flags t <*> exact_no_check (mkVar id)
        else
          exact_check (mkVar id)
      in
      Tacticals.tclFIRST (List.map map hyps)
  end

let unify_e_resolve (flags: Unification.unify_flags) (h: hint): unit tactic =
  Hints.hint_res_pf ~with_evars:true ~with_classes:true ~flags h

let e_exact (h: hint): unit tactic =
  Proofview.Goal.enter begin fun gl ->
    let env = Proofview.Goal.env gl in
    let sigma = Proofview.Goal.sigma gl in
    let sigma, c = Hints.fresh_hint env sigma h in
    Proofview.Unsafe.tclEVARS sigma <*> e_give_exact c
  end

(* All the definitions below are inspired by the coq-core hidden library (i.e not visible in the API) but modified for Waterproof *)

(**
  Cost to solve a hint
*)
type cost = {
  cost_priority : int;
  cost_subgoals : int;
}

(**
  Type alias containing functions that will return a [Hints.hint_db]
*)
type delayed_db = Environ.env -> Evd.evar_map -> hint_db

(**
  State of the search
*)
type search_state = {
  depth: int; (** Depth remaining before failing *)
  tactics_resolution: (Proofview_monad.goal_with_state * delayed_db) list; (** TODO *)
}

(**
  Creates an initial state
*)
let initial_state (evk: Proofview_monad.goal_with_state) (local_db: delayed_db) (n: int): search_state =
  {
    depth = n;
    tactics_resolution = [(evk, local_db)];
  }

let max_depth: int ref = ref 0

(**
  Prints a debug header if [log] is [true]
*)
let pr_dbg_header (trace: trace) = if trace.log then Feedback.msg_notice (str "(* info weauto: *)") else ()

let rec e_trivial_fail_db (trace: trace) (db_list: hint_db list) (local_db: hint_db): unit tactic =
  let next = Proofview.Goal.enter begin fun gl ->
    let d = Declaration.get_id @@ Tacmach.pf_last_hyp gl in
    let local_db = push_resolve_hyp (Tacmach.pf_env gl) (Tacmach.project gl) d local_db in
    e_trivial_fail_db trace db_list local_db
  end in
  Proofview.Goal.enter begin fun gl ->
  let secvars = compute_secvars gl in
  let tacl =
    e_assumption ::
      (Tacticals.tclTHEN Tactics.intro next) ::
      (e_trivial_resolve trace (Tacmach.pf_env gl) (Tacmach.project gl) db_list local_db secvars (Tacmach.pf_concl gl))
  in
  Tacticals.tclSOLVE tacl
  end

and esearch_find (trace: trace) (env: Environ.env) (sigma: Evd.evar_map) (db_list: hint_db list) (local_db: hint_db) (secvars: Id.Pred.t) (concl: types): (unit tactic * cost * Pp.t) list =
  let hint_of_db: hint_db -> FullHint.t list = hintmap_of env sigma secvars concl in
  let flagged_hints: (Unification.unify_flags * FullHint.t) list =
    List.map_append (fun db ->
      let flags = auto_flags_of_state (Hint_db.transparent_state db) in
      List.map (fun x -> (flags, x)) (hint_of_db db)
    ) (local_db::db_list)
  in

  (* Returns a tactic, its priority (which is an approximation of the cost), and its representation from the current state and a [Hints.FullHint.t] *)
  let tac_of_hint ((state, hint): (Unification.unify_flags * FullHint.t)): unit tactic * cost * Pp.t =
    let priority = match FullHint.repr hint with
      | Unfold_nth _ -> 1
      | _ -> FullHint.priority hint
    in let tac: hint hint_ast -> unit tactic = function
      | Res_pf h -> unify_resolve state h
      | ERes_pf h -> unify_e_resolve state h
      | Give_exact h -> e_exact h
      | Res_pf_THEN_trivial_fail h ->
        Tacticals.tclTHEN 
          (unify_e_resolve state h)
          (e_trivial_fail_db trace db_list local_db)
      | Unfold_nth c -> Tactics.reduce (Unfold [(AllOccurrences, c)]) onConcl
      | Extern (pat, tacast) -> conclPattern concl pat tacast
    in
    
    let subgoals = match FullHint.subgoals hint with
      | Some subgoals -> subgoals
      | None -> priority
  in let cost = { cost_priority = priority; cost_subgoals = subgoals } in

    let pr_hint (h: FullHint.t) (env: Environ.env) (sigma: Evd.evar_map): t * t =
      let origin = match FullHint.database h with
      | None -> mt ()
      | Some n -> str n
      in
      (Proofutils.pr_hint env sigma h, origin)
    in
    (* We cannot determine statically the cost of subgoals of an Extern hint, so approximate it by the hint's priority. *)
    let tactic = Proofutils.tclLOG trace (pr_hint hint) @@ FullHint.run hint tac in
    (tactic, cost, FullHint.print env sigma hint)
  in
  List.map tac_of_hint flagged_hints

and e_trivial_resolve (trace: trace) (env: Environ.env) (sigma: Evd.evar_map) (db_list: hint_db list) (local_db: hint_db) (secvars: Id.Pred.t) (gl: types): unit tactic list =
  let filter (tac, pr, _) = if pr.cost_priority = 0 then Some tac else None in
  try List.map_filter filter (esearch_find trace env sigma db_list local_db secvars gl)
  with Not_found -> []

(**
  The goal is solved if the cost of solving is null
*)
let is_solved (cost: cost): bool = cost.cost_subgoals = 0

(* Solved comes first *)
let solve_order (c1: cost) (c2: cost): int = match (is_solved c1, is_solved c2) with
  | (true, true) | (false, false) -> 0
  | (false, true) -> 1
  | (true, false) -> -1

(**
  Compare two states

  Ordering of states is lexicographic:
    1. tactics known to solve the goal
    2. priority
    3. number of generated goals
*)
let compare ((_, c1, _): (unit tactic * cost * Pp.t)) ((_, c2, _): (unit tactic * cost * Pp.t)) =
  let solve_ordering = solve_order c1 c2 in
  let priority_ordering = Int.compare c1.cost_priority c2.cost_priority in
  if solve_ordering != 0 then solve_ordering
  else if priority_ordering != 0 then priority_ordering
  else Int.compare c1.cost_subgoals c2.cost_subgoals

(**
  Returns the list of tactics that will be tried for the proof search

  It always begins with [assumption] and [intros] (not exactly them but equivalent with evar support), then uses the hint databases
*)
let branching (trace: trace) (delayed_database: delayed_db) (dblist: hint_db list) (local_lemmas: Tactypes.delayed_open_constr list): (bool * (Environ.env -> Evd.evar_map -> hint_db) * unit tactic * Pp.t) list tactic =
  Proofview.Goal.enter_one
    begin fun gl ->
      let env = Proofview.Goal.env gl in
      let sigma = Proofview.Goal.sigma gl in
      let concl = Proofview.Goal.concl gl in
      let hyps = EConstr.named_context env in
      let db = delayed_database env sigma in
      let secvars = secvars_of_hyps hyps in
      
      (* Construction of tactics equivalent to [assumption] *)
      let assumption_tacs : (bool * (Environ.env -> Evd.evar_map -> hint_db) * unit tactic * Pp.t) list =

        (* Ensure that no goal is generated *)
        let mkdb (env: Environ.env) (sigma: Evd.evar_map): 'a = assert false in 

        let map_assum (id: variable): (bool * (Environ.env -> Evd.evar_map -> hint_db) * unit tactic * Pp.t) =
          let hint =  str "exact" ++ str " " ++ Id.print id in
          (false, mkdb, Proofutils.tclLOG trace (fun _ _ -> (hint, str "")) @@ e_give_exact (mkVar id), hint)
        in List.map map_assum (ids_of_named_context hyps)
      in

      (* Construction of tactic equivalent to [intros] *)
      let intro_tac: (bool * (Environ.env -> Evd.evar_map -> hint_db) * unit tactic * Pp.t) =
        let mkdb (env: Environ.env) (sigma: Evd.evar_map): hint_db =
          push_resolve_hyp env sigma (Declaration.get_id (List.hd (EConstr.named_context env))) db
        in (false, mkdb, Proofutils.tclLOG trace (fun _ _ -> (str "intro", str "")) Tactics.intro, str "intro")
      in

      let new_trace = incr_trace_depth trace in
      (* Construction of tactics derivated from hint databases *)
      let rec_tacs: (bool * (Environ.env -> Evd.evar_map -> hint_db) * unit tactic * Pp.t) list tactic =
        let mkdb (env: Environ.env) (sigma: Evd.evar_map): hint_db =
          let hyps' = EConstr.named_context env in
          if hyps' == hyps
            then db
            else make_local_hint_db env sigma ~ts:TransparentState.full true local_lemmas
        in try 
          esearch_find new_trace env sigma dblist db secvars concl
            |> List.sort compare
            |> List.map (fun (tac, _, pp) -> (true, mkdb, tac, pp))
            |> Proofview.tclUNIT
        with Not_found -> tclUNIT []
      in
      
      rec_tacs >>= fun rec_tacs ->
      Proofview.tclUNIT (assumption_tacs @ intro_tac :: rec_tacs)
    end

(**
  Actual search function
*)
let resolve_esearch (trace: trace) (dblist: hint_db list) (local_lemmas: Tactypes.delayed_open_constr list) (state: search_state): search_state tactic =
  let rec explore (state: search_state) =
    if state.depth = 0
      then Proofview.tclZERO SearchBound
      else match state.tactics_resolution with
        | [] -> Proofview.tclUNIT state
        | (gl, db) :: rest ->
          Proofview.tclEVARMAP >>= fun sigma ->
          match Proofview.Unsafe.undefined sigma [gl] with
            | [] -> explore { state with tactics_resolution = rest }
            | gl :: _ ->
              Proofview.Unsafe.tclSETGOALS [gl] <*>
              branching trace db dblist local_lemmas >>= fun tacs ->
              let cast ((isrec, mkdb, tac, pp): (bool * delayed_db * unit tactic * Pp.t)): search_state tactic =
                Proofview.tclONCE tac >>= fun () ->
                Proofview.Unsafe.tclGETGOALS >>= fun lgls ->
                Proofview.tclEVARMAP >>= fun sigma ->
                let join (gl: Proofview_monad.goal_with_state): (Proofview_monad.goal_with_state * delayed_db) = (gl, mkdb) in
                let depth =
                  if isrec && not @@ List.is_empty lgls
                    then pred state.depth
                    else state.depth
                in
                Proofview.tclUNIT { depth; tactics_resolution = List.map join lgls @ rest }
              in
              tacs
                |> List.map cast
                |> explore_many

  and explore_many (tactic_list: search_state tactic list) = match tactic_list with
  | [] -> Proofview.tclZERO SearchBound
  | tac :: l -> 
    Proofview.tclORELSE
      (tac >>= fun state -> explore state)
      
      (* discriminate between search failures and [tac] raising an error *)
      (fun e -> explore_many l)
  
  in explore state

(**
  Searches a sequence of at most [n] tactics within [db_list] and [lems] that solves the goal

  The goal can contain evars
*)
let esearch (trace: trace) (depth: int) (lems: Tactypes.delayed_open_constr list) (db_list: hint_db list) =
  Proofview.Goal.enter begin fun gl ->
  let local_db env sigma = make_local_hint_db env sigma ~ts:TransparentState.full true lems in
  let tac (s: search_state): search_state tactic = resolve_esearch trace db_list lems s in
  Proofview.tclORELSE
    begin
      let evk = Proofview.goal_with_state (Proofview.Goal.goal gl) (Proofview.Goal.state gl) in
      tac (initial_state evk local_db depth) >>= fun s ->
      assert (List.is_empty s.tactics_resolution);
      Proofview.Unsafe.tclSETGOALS []
    end
    begin function
    | (SearchBound, _) ->
      pr_info_nop trace;
      Proofview.tclUNIT ()
    | (e, info) -> Proofview.tclZERO ~info e
    end
  end

(**
  Generates the [weauto] function
*)
let gen_weauto (trace: trace) ?(n: int = 5) (lems: Tactypes.delayed_open_constr list) (db_names: hint_db_name list): unit tactic =
  Proofview.wrap_exceptions @@ fun () ->
  let db_list = make_db_list db_names in
  Hints.wrap_hint_warning @@ tcl_try_dbg trace pr_dbg_header @@ esearch trace n lems db_list

(**
  Waterproof eauto

  This function is a rewrite around coq-core.Eauto.eauto with the same arguments to be able to retrieve which tactics have been used in case of success.

  The given [debug] will be updated with the trace at the end of the execution (consider using).

  The code structure has been rearranged to match the one of [Wauto.wauto].
*)
let weauto (trace: trace) (n: int) (lems: Tactypes.delayed_open_constr list) (db_names: hint_db_name list): unit tactic =
  max_depth := n;
  gen_weauto trace ~n lems db_names