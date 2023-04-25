open Hints

(**
  Returns the index of the first element `x` of `l` such that `f x` is `true`
*)
let find_first (f: 'a -> bool) (l: 'a list): int option =
  let rec aux (index: int) (p: 'a list): int option = match p with
    | [] -> None
    | x::q when f x -> Some index
    | _::q -> aux (index + 1) q
  in aux 0 l

(**
  Returns the index of the last element `x` of `l` such that `f x` is `true`
*)
let find_last (f: 'a -> bool) (l: 'a list): int option =
  let rec aux (current_index: int) (last_index: int option) (p: 'a list): int option =
    match p with
      | [] -> last_index
      | x::q ->
        aux (current_index + 1) (if f x then Some current_index else last_index) q
  in aux 0 None l

(**
  Returns the queue of the given list after the `n`th element included
*)
let rec tail_end (l: 'a list) (n: int): 'a list = match (l, n) with
  | (_, 0) -> l
  | ([], _) -> []
  | (_::p, _) -> tail_end p (n - 1)

(**
  Wrapper around `Proofview.tclTHEN` who actually execute the first tactic before the second
*)
let tclRealThen (first: unit Proofview.tactic) (second: unit Proofview.tactic lazy_t): unit Proofview.tactic =
  Proofview.tclBIND first (fun () -> Proofview.tclTHEN (Proofview.tclUNIT ()) (Lazy.force second))

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
    | Unfold_nth c -> Printer.pr_evaluable_reference c
    | Extern (_, tac) -> Pputils.pr_glb_generic env sigma tac