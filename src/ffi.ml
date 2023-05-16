(**
  Small wrapper around Ltac2/OCaml Foreign Function Interface (FFI)

  This allows Ltac2 to call OCaml-defined functions
*)

module Tac2ffi = Ltac2_plugin.Tac2ffi
module Tac2env = Ltac2_plugin.Tac2env
module Tac2expr = Ltac2_plugin.Tac2expr

open Proofview
open Tac2expr
open Tac2ffi

(** Creates a name used to define the function interface *)
let pname (s: string): ml_tactic_name = { mltac_plugin = "coq-core.plugins.coq-waterproof"; mltac_tactic = s }

(** Wrapper around {! Tac2env.define_primitive} to make easier the primitive definition *)
let define_primitive (name: string) (arity: 'a arity) (f: 'a): unit =
  Tac2env.define_primitive (pname name) (mk_closure arity f)

(** 
  Defines a function of arity 0 (that only take a [unit] as an argument)

  This function will be callable in Ltac2 with [Ltac2 @ external <ltac2_name>: unit := "coq-waterproof" "<name>".]
*)
let define0 (name: string) (f: valexpr tactic): unit = define_primitive name arity_one (fun _ -> f)

(** 
  Defines a function of arity 1 (that only take one argument)

  This function will be callable in Ltac2 with [Ltac2 @ external <ltac2_name>: <type> -> unit := "coq-waterproof" "<name>".]
*)
let define1 (name: string) (r0: 'a repr) (f: 'a -> valexpr tactic): unit =
  define_primitive name arity_one @@ fun x -> f (repr_to r0 x)

(** 
  Defines a function of arity 2 of the same way than {! define1}
*)
let define2 (name: string) (r0: 'a repr) (r1: 'b repr) (f: 'a -> 'b -> valexpr tactic): unit =
  define_primitive name (arity_suc arity_one) @@ fun x y -> f (repr_to r0 x) (repr_to r1 y)

(** 
  Defines a function of arity 3 of the same way than {! define1}
*)
let define3 (name: string) (r0: 'a repr) (r1: 'b repr) (r2: 'c repr) (f: 'a -> 'b -> 'c -> valexpr tactic): unit =
  define_primitive name (arity_suc (arity_suc arity_one)) @@ fun x y z -> f (repr_to r0 x) (repr_to r1 y) (repr_to r2 z)

(** 
  Defines a function of arity 4 of the same way than {! define1}
*)
let define4 (name: string) (r0: 'a repr) (r1: 'b repr) (r2: 'c repr) (r3: 'd repr) (f: 'a -> 'b -> 'c -> 'd -> valexpr tactic): unit =
  define_primitive name (arity_suc (arity_suc (arity_suc arity_one))) @@
  fun x0 x1 x2 x3 -> f (repr_to r0 x0) (repr_to r1 x1) (repr_to r2 x2) (repr_to r3 x3)

(** 
  Defines a function of arity 5 of the same way than {! define1}
*)
let define5 (name: string) (r0: 'a repr) (r1: 'b repr) (r2: 'c repr) (r3: 'd repr) (r4: 'e repr) (f: 'a -> 'b -> 'c -> 'd -> 'e -> valexpr tactic): unit =
  define_primitive name (arity_suc (arity_suc (arity_suc (arity_suc arity_one)))) @@
  fun x0 x1 x2 x3 x4 -> f (repr_to r0 x0) (repr_to r1 x1) (repr_to r2 x2) (repr_to r3 x3) (repr_to r4 x4)

(** Comes from [coq/plugins/ltac2/tac2tactics.ml] *)
let thaw (r: 'a repr) (f: (unit, 'a) fun1): 'a tactic = app_fun1 f unit r ()

(** Comes from [coq/plugins/ltac2/tac2tactics.ml] *)
let delayed_of_tactic (tac: 'a tactic) (env: Environ.env) (sigma: Evd.evar_map): (Evd.evar_map * 'a) =
  let _, pv = Proofview.init sigma [] in
  let name, poly = Names.Id.of_string "ltac2_delayed", false in
  let c, pv, _, _ = Proofview.apply ~name ~poly env tac pv in
  let _, sigma = Proofview.proofview pv in
  (sigma, c)


(**
  Utilitary function to cast OCaml types into Ltac2-compatibles types  
  
  Comes from [coq/plugins/ltac2/tac2tactics.ml]
*)
let delayed_of_thunk (r: 'a repr) (tac: (unit, 'a) fun1) (env: Environ.env) (sigma: Evd.evar_map): (Evd.evar_map * 'a) =
  delayed_of_tactic (thaw r tac) env sigma