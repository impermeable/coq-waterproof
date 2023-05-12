(**
  Searches a sequence of at most [n] tactics within [db_list] and [lems] that solves the goal

  The goal can contain evars
*)
val esearch :
  bool ->
  int ->
  Tactypes.delayed_open_constr list ->
  Hints.hint_db list ->
  Backtracking.trace Proofview.tactic

(**
  Waterproof eauto

  This function is a rewrite around coq-core.Eauto.eauto with the same arguments to be able to retrieve which tactics have been used in case of success.

  The given [debug] will be updated with the trace at the end of the execution (consider using).

  The code structure has been rearranged to match the one of [Wauto.wauto].
*)
val weauto :
  bool ->
  int ->
  Tactypes.delayed_open_constr list ->
  string list ->
  Backtracking.trace Proofview.tactic

(**
  Restricted Waterproof eauto

  This function acts the same as {! wauto} but will fail if all proof found contain at least one must-use lemma that is unused or one hint that is in the [forbidden] list.
*)
val rweauto :
  bool ->
  int ->
  Tactypes.delayed_open_constr list ->
  Hints.hint_db_name list ->
  Pp.t list ->
  Pp.t list ->
  Backtracking.trace Proofview.tactic