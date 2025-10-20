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
open Ltac2_plugin.Tac2externals

open Proofview
open Tac2expr
open Tac2ffi
open Ltac2_plugin.Tac2val

open Exceptions
open Hint_dataset_declarations
open Waterprove
open Wp_evars

(** Creates a name used to define the function interface *)
let pname (s: string): ml_tactic_name = { mltac_plugin = "rocq-runtime.plugins.coq-waterproof"; mltac_tactic = s }

let define s = Ltac2_plugin.Tac2externals.define (pname s)

(** Comes from [coq/plugins/ltac2/tac2tactics.ml] *)
let thaw (r: 'a repr) (f: (unit, 'a) fun1): 'a tactic = app_fun1 f unit r ()

(** Comes from [coq/plugins/ltac2/tac2tactics.ml] *)
let delayed_of_tactic (tac: 'a tactic) (env: Environ.env) (sigma: Evd.evar_map): (Evd.evar_map * 'a) =
  let _, pv = Proofview.init sigma [] in
  let name, poly = Names.Id.of_string "ltac2_delayed", false in
  let c, pv, _, _= Proofview.apply ~name ~poly env tac pv in
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

(** Converts a {! Hint_dataset_declarations.database_type} into a [valexpr] *)
let of_database_type (database_type: database_type): valexpr = match database_type with
  | Main -> ValInt 0
  | Decidability -> ValInt 1
  | Shorten -> ValInt 2

(** Converts a [valexpr] into a {! Hint_dataset_declarations.database_type} *)
let to_database_type (value: valexpr): database_type = match value with
  | ValInt n ->
    let database_type = match n with
      | 0 -> Main
      | 1 -> Decidability
      | 2 -> Shorten
      | _ -> throw (CastError "cannot cast something an [int] greater than 3 into a [database_type]")
    in database_type
  | _ -> throw (CastError "cannot cast something different than an [int] into a [database_type]")

let database_type = make_repr of_database_type to_database_type

(** Converts a {! Feedback.level} into a [valexpr] *)
let of_feedback_level (feedback_lvl: Feedback.level): valexpr = match feedback_lvl with
  | Debug -> ValInt (-1)
  | Info -> ValInt 0
  | Notice -> ValInt 1
  | Warning -> ValInt 2
  | Error -> ValInt 3

(** Converts a [valexpr] into a {! Feedback.level} *)
let to_feedback_level (value : valexpr): Feedback.level = match value with
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

let feedback_level = make_repr of_feedback_level to_feedback_level

(* Exports {! Waterprove.waterprove} to Ltac2 *)
let () =
  define "waterprove" (int @-> bool @-> (list (thunk constr)) @-> database_type @-> tac unit) @@
    fun depth shield lems database_type ->
      begin
        waterprove
          depth
          ~shield
          (List.map (fun lem -> delayed_of_thunk constr lem) lems)
          database_type
      end

(* Exports {! Waterprove.rwaterprove} to Ltac2 *)
let () =
  define "rwaterprove" (int @-> bool @-> (list (thunk constr))
      @-> database_type @-> list constr @-> list constr @-> tac unit) @@
    fun depth shield lems database_type must_use forbidden ->
      begin
        rwaterprove
          depth
          ~shield
          (List.map (fun lem -> delayed_of_thunk constr lem) lems)
          database_type
          must_use
          forbidden
      end

let () =
  define "warn_external" (pp @-> tac unit) @@
    warn

let () =
  define "notice_external" (pp @-> tac unit) @@
    notice

let () =
  define "throw_external" (pp @-> tac unit) @@
    err

let () =
  define "inform_external" (pp @-> tac unit) @@
    inform

let () =
  define "message_external" (feedback_level @-> pp @-> (tac unit)) @@
    message

let () =
  define "refine_goal_with_evar_external" (string @-> tac unit) @@
    refine_goal_with_evar

let () =
  define "blank_evars_in_term_external" (constr @-> tac (list evar)) @@
    blank_evars_in_term

let () =
  define "get_print_hypothesis_flag_external" (unit @-> ret bool) @@
    fun () -> !print_hypothesis_help

let () =
  define "get_redirect_errors_flag_external" (unit @-> ret bool) @@
    fun () -> !redirect_errors

let () =
  define "get_last_warning_external" (unit @-> ret (option pp)) @@
    get_last_warning

let () =
  define "get_feedback_log_external" (feedback_level @-> ret (list pp)) @@
    fun input -> !(feedback_log input)
