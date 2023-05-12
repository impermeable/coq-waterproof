(**
  Returns the index of the first element [x] of [l] such that `f x` is [true]
*)
val find_first : ('a -> bool) -> 'a list -> int option

(**
  Returns the index of the last element [x] of [l] such that `f x` is [true]
*)
val find_last : ('a -> bool) -> 'a list -> int option

(**
  Returns the queue of the given list after the [n]th element included
*)
val tail_end : 'a list -> int -> 'a list

(**
  Generic dictionnary taking strings as keys
*)
module StringMap : sig
  type key = string
  type 'a t = 'a Map.Make(String).t

  val empty : 'a t
  val is_empty : 'a t -> bool
  val mem : key -> 'a t -> bool
  val add : key -> 'a -> 'a t -> 'a t
  val update : key -> ('a option -> 'a option) -> 'a t -> 'a t
  val singleton : key -> 'a -> 'a t
  val remove : key -> 'a t -> 'a t

  val merge :
    (key -> 'a option -> 'b option -> 'c option) ->
    'a t ->
    'b t ->
    'c t

  val union :
    (key -> 'a -> 'a -> 'a option) -> 'a t -> 'a t -> 'a t

  val compare : ('a -> 'a -> int) -> 'a t -> 'a t -> int
  val equal : ('a -> 'a -> bool) -> 'a t -> 'a t -> bool
  val iter : (key -> 'a -> unit) -> 'a t -> unit
  val fold : (key -> 'a -> 'b -> 'b) -> 'a t -> 'b -> 'b
  val for_all : (key -> 'a -> bool) -> 'a t -> bool
  val exists : (key -> 'a -> bool) -> 'a t -> bool
  val filter : (key -> 'a -> bool) -> 'a t -> 'a t
  val filter_map : (key -> 'a -> 'b option) -> 'a t -> 'b t
  val partition : (key -> 'a -> bool) -> 'a t -> 'a t * 'a t
  val cardinal : 'a t -> int
  val bindings : 'a t -> (key * 'a) list
  val min_binding : 'a t -> key * 'a
  val min_binding_opt : 'a t -> (key * 'a) option
  val max_binding : 'a t -> key * 'a
  val max_binding_opt : 'a t -> (key * 'a) option
  val choose : 'a t -> key * 'a
  val choose_opt : 'a t -> (key * 'a) option
  val split : key -> 'a t -> 'a t * 'a option * 'a t
  val find : key -> 'a t -> 'a
  val find_opt : key -> 'a t -> 'a option
  val find_first : (key -> bool) -> 'a t -> key * 'a

  val find_first_opt :
    (key -> bool) -> 'a t -> (key * 'a) option

  val find_last : (key -> bool) -> 'a t -> key * 'a

  val find_last_opt :
    (key -> bool) -> 'a t -> (key * 'a) option

  val map : ('a -> 'b) -> 'a t -> 'b t
  val mapi : (key -> 'a -> 'b) -> 'a t -> 'b t
  val to_seq : 'a t -> (key * 'a) Seq.t
  val to_rev_seq : 'a t -> (key * 'a) Seq.t
  val to_seq_from : key -> 'a t -> (key * 'a) Seq.t
  val add_seq : (key * 'a) Seq.t -> 'a t -> 'a t
  val of_seq : (key * 'a) Seq.t -> 'a t
end

(**
  Wrapper around [Proofview.tclTHEN] who actually execute the first tactic before the second
*)
val tclRealThen :
  unit Proofview.tactic ->
  'a Proofview.tactic lazy_t ->
  'a Proofview.tactic

(**
  Rewrite of [Auto.tclLOG]

  Updates the trace contained in the given tactic.

  Fails if the hint's name is forbidden, or if the proof will be complete without using all must-use lemmas.
*)
val tclLOG :
  (Environ.env -> Evd.evar_map -> Pp.t * Pp.t) ->
  Backtracking.trace Proofview.tactic ->
  Pp.t list ->
  Backtracking.trace Proofview.tactic

(**
  Checks if every hint in [must_use] is contained in [tac] and returns an exception if not
*)
val trace_check_used :
  Pp.t list ->
  Backtracking.trace ->
  Backtracking.trace Proofview.tactic

(**
  Wrapper around {! Proofview.tclTHEN} with a merge of tactics' traces
*)
val tclTraceThen :
  Backtracking.trace Proofview.tactic ->
  Backtracking.trace Proofview.tactic ->
  Backtracking.trace Proofview.tactic

(**
  Merge a list of traces contained in a tactic into one trace

  Useful to combine with {! Proofview.tclINDEPENDENTL}
*)
val tclAggregateTraces :
  Backtracking.trace list Proofview.tactic ->
  Backtracking.trace Proofview.tactic

(**
  Wrapper around {! Proofview.Goal.enter} to allow [Backtracking.trace tactic] and not just [unit tactic]
*)
val trace_goal_enter :
  (Proofview.Goal.t -> Backtracking.trace Proofview.tactic) ->
  Backtracking.trace Proofview.tactic

(**
  Rewrite of {! Tacticals.tclORELSE0} to give the trace of the failed tactic instead of the exception
*)
val tclOrElse0 :
  Backtracking.trace Proofview.tactic ->
  (Backtracking.trace -> Backtracking.trace Proofview.tactic) ->
  Backtracking.trace Proofview.tactic

(**
  Wrapper around {! tclOrElse0} with merge of trace contained in the failed [trace tactic] into the second one
*)
val tclTraceOrElse :
  Backtracking.trace Proofview.tactic ->
  Backtracking.trace Proofview.tactic ->
  Backtracking.trace Proofview.tactic

(**
  Rewrite of {! Tacticals.tclTraceFirst} with [trace tactic] with a merge of traces of failed tactics 
*)
val tclTraceFirst :
  Backtracking.trace Proofview.tactic list ->
  Backtracking.trace Proofview.tactic

(**
  Rewrite of Coq's hint printer to keep only the necessary parts
*)
val pr_hint :
  Environ.env -> Evd.evar_map -> Hints.FullHint.t -> Pp.t
