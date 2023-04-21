type debug =
  Hints.debug
  * int
  * (int
    * (Environ.env -> Evd.evar_map -> Pp.t * Pp.t) option
    * Pp.t
    * Pp.t)
    list
    ref

val new_debug : Hints.debug -> debug

val wauto :
  debug ->
  int ->
  Tactypes.delayed_open_constr list ->
  string list ->
  unit Proofview.tactic