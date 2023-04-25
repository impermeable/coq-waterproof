(**
  Returns the index of the first element `x` of `l` such that `f x` is `true`
*)
val find_first : ('a -> bool) -> 'a list -> int option

(**
  Returns the index of the last element `x` of `l` such that `f x` is `true`
*)
val find_last : ('a -> bool) -> 'a list -> int option

(**
  Returns the queue of the given list after the `n`th element included
*)
val tail_end : 'a list -> int -> 'a list

(**
  Wrapper around `Proofview.tclTHEN` who actually execute the first tactic before the second

  Can be rewrite in a more clear form
*)
val tclRealThen :
  unit Proofview.tactic ->
  unit Proofview.tactic lazy_t ->
  unit Proofview.tactic

(**
  Rewrite of Coq's hint printer to keep only the necessary parts
*)
val pr_hint :
  Environ.env -> Evd.evar_map -> Hints.FullHint.t -> Pp.t