val tclRealThen :
  unit Proofview.tactic ->
  unit Proofview.tactic lazy_t ->
  unit Proofview.tactic

val pr_hint :
  Environ.env -> Evd.evar_map -> Hints.FullHint.t -> Pp.t
