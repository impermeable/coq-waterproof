open Hints
open Pp

(**
  Wrapper around `Proofview.tclTHEN` who actually execute the first tactic before the second

  Can be rewrite in a more clear form
*)
let tclRealThen (first: unit Proofview.tactic) (second: unit Proofview.tactic lazy_t): unit Proofview.tactic =
  Proofview.tclBIND first (fun () -> Proofview.tclTHEN first (Lazy.force second))

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
    | Unfold_nth c -> str"unfold " ++ Printer.pr_evaluable_reference c
    | Extern (_, tac) -> Pputils.pr_glb_generic env sigma tac