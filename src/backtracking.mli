(**
  Returns the trace atoms that have been actually applied during [wauto]

  It is supposed here that the given [trace] has not been modified since the end of [wauto] and that [wauto] is successful, i.e it succeed to solve the goal
*)
val keep_applied :
  Wauto.trace_atom list -> (int * Pp.t * Pp.t) list
