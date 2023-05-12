open Backtracking

(**
  Same function as {! Auto.exists_evaluable_reference}
*)
val exists_evaluable_reference : Environ.env -> Tacred.evaluable_global_reference -> bool

(**
  Prints "idtac" if the [log] field is [true]
*)
val pr_info_nop : unit -> unit

(**
  Tries the given tactic and calls an info printer if it fails
*)
val tclTryDbg :
  (unit -> unit) ->
  trace Proofview.tactic ->
  trace Proofview.tactic

(**
  Creates a function that takes a hint database and returns a hint list
*)
val hintmap_of :
  Environ.env ->
  Evd.evar_map ->
  Names.Id.Pred.t ->
  Evd.econstr ->
  (Hints.hint_db -> Hints.FullHint.t list)

(**
  Searches a sequence of at most [n] tactics within [db_list] and [lems] that solves the goal

  The goal cannot contain evars
*)
val search :
  Backtracking.trace ->
  int ->
  Tactypes.delayed_open_constr list ->
  Hints.hint_db list ->
  Backtracking.trace Proofview.tactic

(**
  Waterproof auto

  This function is a rewrite around coq-core.Auto.auto with the same arguments to be able to retrieve which tactics have been used in case of success.

  Returns a typed tactic containing the full trace
*)
val wauto :
  bool ->
  int ->
  Tactypes.delayed_open_constr list ->
  string list ->
  Backtracking.trace Proofview.tactic

(**
  Restricted Waterproof auto

  This function acts the same as {! wauto} but will fail if all proof found contain at least one must-use lemma that is unused or one hint that is in the [forbidden] list.
*)
val rwauto :
  bool ->
  int ->
  Tactypes.delayed_open_constr list ->
  string list ->
  Pp.t list ->
  Pp.t list ->
  Backtracking.trace Proofview.tactic
