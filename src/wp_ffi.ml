(******************************************************************************)
(*                  This file is part of Waterproof-lib.                      *)
(*                                                                            *)
(*   Waterproof-lib is free software: you can redistribute it and/or modify   *)
(*    it under the terms of the GNU General Public License as published by    *)
(*     the Free Software Foundation, either version 3 of the License, or      *)
(*                    (at your option) any later version.                     *)
(*                                                                            *)
(*     Waterproof-lib is distributed in the hope that it will be useful,      *)
(*      but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*       MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the         *)
(*               GNU General Public License for more details.                 *)
(*                                                                            *)
(*     You should have received a copy of the GNU General Public License      *)
(*   along with Waterproof-lib. If not, see <https://www.gnu.org/licenses/>.  *)
(*                                                                            *)
(******************************************************************************)

(** Functions that should be available from Ltac2 can be made available from here
*)

module Tac2ffi = Ltac2_plugin.Tac2ffi
module Tac2env = Ltac2_plugin.Tac2env
module Tac2expr = Ltac2_plugin.Tac2expr

open Proofview
open Proofview.Notations
open Tac2expr
open Tac2ffi

open Exceptions
open Hint_dataset_declarations
open Waterprove
open Wp_evars

(** Creates a name used to define the function interface *)
let pname (s: string): ml_tactic_name = { mltac_plugin = "coq-core.plugins.coq-waterproof"; mltac_tactic = s }

(** Wrapper around {! Tac2env.define_primitive} to make easier the primitive definition *)
let define_primitive (name: string) (arity: 'a arity) (f: 'a): unit =
  Tac2env.define_primitive (pname name) (mk_closure arity f)

(** 
  Defines a function of arity 0 (that only takes a [unit] as an argument)

  This function will be callable in Ltac2 with [Ltac2 @ external <ltac2_name>: unit := "coq-waterproof" "<name>".]
*)
let define0 (name: string) (f: valexpr tactic): unit = define_primitive name arity_one (fun _ -> f)

(** 
  Defines a function of arity 1 (that only takes one argument)

  This function will be callable in Ltac2 with [Ltac2 @ external <ltac2_name>: <type> -> unit := "coq-waterproof" "<name>".]
*)
let define1 (name: string) (r0: 'a repr) (f: 'a -> valexpr tactic): unit =
  define_primitive name arity_one @@ fun x -> f (repr_to r0 x)

(** 
  Defines a function of arity 2 in the same way as {! define1}
*)
let define2 (name: string) (r0: 'a repr) (r1: 'b repr) (f: 'a -> 'b -> valexpr tactic): unit =
  define_primitive name (arity_suc arity_one) @@ fun x y -> f (repr_to r0 x) (repr_to r1 y)

(** 
  Defines a function of arity 3 in the same way as {! define1}
*)
let define3 (name: string) (r0: 'a repr) (r1: 'b repr) (r2: 'c repr) (f: 'a -> 'b -> 'c -> valexpr tactic): unit =
  define_primitive name (arity_suc (arity_suc arity_one)) @@ fun x y z -> f (repr_to r0 x) (repr_to r1 y) (repr_to r2 z)

(** 
  Defines a function of arity 4 in the same way as {! define1}
*)
let define4 (name: string) (r0: 'a repr) (r1: 'b repr) (r2: 'c repr) (r3: 'd repr) (f: 'a -> 'b -> 'c -> 'd -> valexpr tactic): unit =
  define_primitive name (arity_suc (arity_suc (arity_suc arity_one))) @@
  fun x0 x1 x2 x3 -> f (repr_to r0 x0) (repr_to r1 x1) (repr_to r2 x2) (repr_to r3 x3)

(** 
  Defines a function of arity 5 in the same way as {! define1}
*)
let define5 (name: string) (r0: 'a repr) (r1: 'b repr) (r2: 'c repr) (r3: 'd repr) (r4: 'e repr) (f: 'a -> 'b -> 'c -> 'd -> 'e -> valexpr tactic): unit =
  define_primitive name (arity_suc (arity_suc (arity_suc (arity_suc arity_one)))) @@
  fun x0 x1 x2 x3 x4 -> f (repr_to r0 x0) (repr_to r1 x1) (repr_to r2 x2) (repr_to r3 x3) (repr_to r4 x4)

(** 
  Defines a function of arity 6 in the same way as {! define1}
*)
let define6 (name: string) (r0: 'a repr) (r1: 'b repr) (r2: 'c repr) (r3: 'd repr) (r4: 'e repr) (r5: 'f repr) (f: 'a -> 'b -> 'c -> 'd -> 'e -> 'f -> valexpr tactic): unit =
  define_primitive name (arity_suc (arity_suc (arity_suc (arity_suc (arity_suc arity_one))))) @@
  fun x0 x1 x2 x3 x4 x5 -> f (repr_to r0 x0) (repr_to r1 x1) (repr_to r2 x2) (repr_to r3 x3) (repr_to r4 x4) (repr_to r5 x5)

(** 
  Defines a function of arity 7 in the same way as {! define1}
*)
let define7 (name: string) (r0: 'a repr) (r1: 'b repr) (r2: 'c repr) (r3: 'd repr) (r4: 'e repr) (r5: 'f repr) (r6: 'g repr) (f: 'a -> 'b -> 'c -> 'd -> 'e -> 'f -> 'g -> valexpr tactic): unit =
  define_primitive name (arity_suc (arity_suc (arity_suc (arity_suc (arity_suc (arity_suc arity_one)))))) @@
  fun x0 x1 x2 x3 x4 x5 x6 -> f (repr_to r0 x0) (repr_to r1 x1) (repr_to r2 x2) (repr_to r3 x3) (repr_to r4 x4) (repr_to r5 x5) (repr_to r6 x6)

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
  Utility function to cast OCaml types into Ltac2-compatibles types  
  
  Comes from [coq/plugins/ltac2/tac2tactics.ml]
*)
let delayed_of_thunk (r: 'a repr) (tac: (unit, 'a) fun1) (env: Environ.env) (sigma: Evd.evar_map): (Evd.evar_map * 'a) =
  delayed_of_tactic (thaw r tac) env sigma

(** Converts a ['a repr] into a [(unit -> 'a) repr] *)
let thunk (r: 'a repr): (unit, 'a) fun1 repr = fun1 unit r

let _ = define0
let _ = define1
let _ = define2
let _ = define3
let _ = define5
let _ = define7

(** Converts a {! Hint_dataset_declarations.database_type} into a [valexpr] *)
let database_type_to_valexp (database_type: database_type): valexpr = match database_type with
  | Main -> ValInt 0
  | Decidability -> ValInt 1
  | Shorten -> ValInt 2
  
(** Converts a [valexpr] into a {! Hint_dataset_declarations.database_type} *)
let database_type_from_valexp (value: valexpr): database_type = match value with
  | ValInt n ->
    let database_type = match n with
      | 0 -> Main
      | 1 -> Decidability
      | 2 -> Shorten
      | _ -> throw (CastError "cannot cast something an [int] greater than 3 into a [database_type]")
    in database_type
  | _ -> throw (CastError "cannot cast something different than an [int] into a [database_type]")

(* Exports {! Hint_dataset_declarations.database_type} to Ltac2 *)
let () =
  define0 "database_type_main" @@ tclUNIT @@ database_type_to_valexp Main;
  define0 "database_type_decidability" @@ tclUNIT @@ database_type_to_valexp Decidability;
  define0 "database_type_shorten" @@ tclUNIT @@ database_type_to_valexp Shorten

(** Converts a {! Feedback.level} into a [valexpr] *)
let feedback_lvl_to_valexpr (feedback_lvl: Feedback.level): valexpr = match feedback_lvl with
  | Debug -> ValInt (-1)
  | Info -> ValInt 0
  | Notice -> ValInt 1
  | Warning -> ValInt 2
  | Error -> ValInt 3

(** Converts a [valexpr] into a {! Feedback.level} *)
let feedback_lvl_from_valexpr (value : valexpr): Feedback.level = match value with
  | ValInt n ->
    let feedback_lvl = match n with
      | -1 -> Feedback.Debug
      | 0 -> Info
      | 1 -> Notice
      | 2 -> Warning
      | 3 -> Error
      | _ -> throw (CastError "cannot cast an [int] outside {-1, 0, 1, 2, 3} into a [Feedback.level]")
    in feedback_lvl
  | _ -> throw (CastError "cannot cast something different from an [int] into a [Feedback.level]")

(** Pack the conversion functions for feedback levels into a representation *)
let feedback_lvl_repr = make_repr feedback_lvl_to_valexpr feedback_lvl_from_valexpr

(** Exports {! Feedback.level} to Ltac2 *)
let () =
  define0 "feedback_lvl_debug" @@ tclUNIT @@ feedback_lvl_to_valexpr Feedback.Debug;
  define0 "feedback_lvl_info" @@ tclUNIT @@ feedback_lvl_to_valexpr Feedback.Info;
  define0 "feedback_lvl_notice" @@ tclUNIT @@ feedback_lvl_to_valexpr Feedback.Notice;
  define0 "feedback_lvl_warning" @@ tclUNIT @@ feedback_lvl_to_valexpr Feedback.Warning;
  define0 "feedback_lvl_error" @@ tclUNIT @@ feedback_lvl_to_valexpr Feedback.Error

(* Exports {! Waterprove.waterprove} to Ltac2 *)
let () =
  define4 "waterprove" int bool (list (thunk constr)) (make_repr database_type_to_valexp database_type_from_valexp) @@
    fun depth shield lems database_type ->
      begin
        waterprove
          depth
          ~shield
          (List.map (fun lem -> delayed_of_thunk constr lem) lems)
          database_type
      end >>= fun () -> tclUNIT @@ of_unit ()

(* Exports {! Waterprove.rwaterprove} to Ltac2 *)
let () =
  define6 "rwaterprove" int bool (list (thunk constr)) (make_repr database_type_to_valexp database_type_from_valexp) (list constr) (list constr) @@
    fun depth shield lems database_type must_use forbidden ->
      begin
        rwaterprove
          depth
          ~shield
          (List.map (fun lem -> delayed_of_thunk constr lem) lems)
          database_type
          must_use
          forbidden
      end >>= fun () -> tclUNIT @@ of_unit ()

let () =
  define1 "warn_external" pp @@ 
    fun input ->
      warn input >>= fun () -> tclUNIT @@ of_unit ()

let () =
  define1 "notice_external" pp @@
    fun input ->
      notice input >>= fun () -> tclUNIT @@ of_unit ()

let () =
  define1 "throw_external" pp @@
    fun input ->
      err input >>= fun () -> tclUNIT @@ of_unit ()

let () =
  define1 "inform_external" pp @@
    fun input ->
      inform input >>= fun () -> tclUNIT @@ of_unit ()

let () =
  define2 "message_external" feedback_lvl_repr pp @@
    fun lvl input ->
      message lvl input >>= fun () -> tclUNIT @@ of_unit ()

let () =
  define1 "refine_goal_with_evar_external" string @@
    fun input -> refine_goal_with_evar input >>= fun () -> tclUNIT @@ of_unit ()

let () =
  define1 "blank_evars_in_term_external" constr @@
    fun term ->
      blank_evars_in_term term >>=
      fun evars -> tclUNIT @@ (of_list of_evar evars)

let () =
  define1 "get_print_hypothesis_flag_external" unit @@
    fun input -> tclUNIT @@ of_bool !print_hypothesis_help

let () =
  define1 "get_redirect_errors_flag_external" unit @@
    fun input -> tclUNIT @@ of_bool !redirect_errors

let () =
  define1 "get_last_warning_external" unit @@
    fun input -> get_last_warning input >>=
      fun pp_option -> tclUNIT @@ of_option of_pp pp_option

let () =
  define1 "get_feedback_log_external" feedback_lvl_repr @@
    fun input -> tclUNIT @@ of_list of_pp !(feedback_log input)
