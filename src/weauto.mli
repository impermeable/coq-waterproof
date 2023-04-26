(**
  Waterproof eauto

  This function is a rewrite around coq-core.Eauto.eauto with the same arguments to be able to retrieve which tactics have been used in case of success.

  The given `debug` will be updated with the trace at the end of the execution (consider using).

  The code structure has been rearranged to match the one of `Wauto.wauto`.
*)
val weauto :
  Wauto.debug ->
  int ->
  Tactypes.delayed_open_constr list ->
  string list ->
  unit Proofview.tactic
