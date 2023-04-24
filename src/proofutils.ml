(**
  Wrapper around `Proofview.tclTHEN` who actually execute the first tactic before the second 
*)
let tclRealThen (first: unit Proofview.tactic) (second: unit Proofview.tactic lazy_t): unit Proofview.tactic =
  Proofview.tclBIND first (fun () -> Proofview.tclTHEN first (Lazy.force second))