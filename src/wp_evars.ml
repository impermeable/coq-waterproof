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

open Ltac2_plugin.Tac2ffi
open Ltac2_plugin.Tac2env
open Ltac2_plugin.Tac2expr
open Ltac2_plugin.Tac2entries

open Pp
open Proofview
open Proofview.Notations
open Util
open Names
open Genarg

open Exceptions
open Hint_dataset_declarations
open Waterprove

(** Creates a name used to define the function interface *)
let pname (s: string): ml_tactic_name = { mltac_plugin = "coq-core.plugins.coq-waterproof"; mltac_tactic = s }

(** Wrapper around {! Tac2env.define_primitive} to make easier the primitive definition *)
let define_primitive (name: string) (arity: 'a arity) (f: 'a) : unit =
  define_primitive (pname name) (mk_closure arity f)

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
  define_primitive name arity_one begin fun x -> f (repr_to r0 x) end

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

(** 
  Defines a function of arity 6 of the same way than {! define1}
*)
let define6 (name: string) (r0: 'a repr) (r1: 'b repr) (r2: 'c repr) (r3: 'd repr) (r4: 'e repr) (r5: 'f repr) (f: 'a -> 'b -> 'c -> 'd -> 'e -> 'f -> valexpr tactic): unit =
  define_primitive name (arity_suc (arity_suc (arity_suc (arity_suc (arity_suc arity_one))))) @@
  fun x0 x1 x2 x3 x4 x5 -> f (repr_to r0 x0) (repr_to r1 x1) (repr_to r2 x2) (repr_to r3 x3) (repr_to r4 x4) (repr_to r5 x5)

(** 
  Defines a function of arity 7 of the same way than {! define1}
*)
let define7 (name: string) (r0: 'a repr) (r1: 'b repr) (r2: 'c repr) (r3: 'd repr) (r4: 'e repr) (r5: 'f repr) (r6: 'g repr) (f: 'a -> 'b -> 'c -> 'd -> 'e -> 'f -> 'g -> valexpr tactic): unit =
  define_primitive name (arity_suc (arity_suc (arity_suc (arity_suc (arity_suc (arity_suc arity_one)))))) @@
  fun x0 x1 x2 x3 x4 x5 x6 -> f (repr_to r0 x0) (repr_to r1 x1) (repr_to r2 x2) (repr_to r3 x3) (repr_to r4 x4) (repr_to r5 x5) (repr_to r6 x6)

(**
  Utilitary function to cast OCaml types into Ltac2-compatibles types  
  
  Comes from [coq/plugins/ltac2/tac2tactics.ml]
*)

let _ = define0
let _ = define1
let _ = define2
let _ = define3
let _ = define5
let _ = define7

let return x = Proofview.tclUNIT x

let wrap_unit f =
  return

(**
  Print an overview of the present evars
*)
let print_evars : valexpr tactic =
  tclEVARMAP >>= fun sigma ->
      tclUNIT @@ of_unit @@
      if Evd.has_undefined sigma then
        Feedback.msg_warning (str "there are undefined evars")
      else
        Feedback.msg_warning (str "there are no undefined evars")

(** 
  Should print information about an evar, now only returns 5
*)
let print_evar_info (input : Evar.t) : valexpr tactic =
  tclEVARMAP >>= fun sigma -> Proofview.tclUNIT @@ of_unit @@
    let (l, k) = (Evd.evar_source (Evd.find sigma input)) in
    match k with
    | Evar_kinds.InternalHole -> Feedback.msg_warning (str "The evar is an internal hole")
    | Evar_kinds.NamedHole _ -> Feedback.msg_warning (str "The evar is a named hole")
    | _ -> Feedback.msg_warning (str "Not an internal or named hole")

let is_internal_hole (ev_map : Evd.evar_map) (input : Evar.t) : bool =
  let (l, k) = (Evd.evar_source (Evd.find ev_map input)) in
  match k with
  | Evar_kinds.QuestionMark _ -> true
  | _ -> false

let find_evars_in_term (term : Evd.econstr) :
  valexpr tactic =
  tclEVARMAP >>= fun sigma -> Proofview.tclUNIT @@ of_unit @@
    let evars = Evarutil.undefined_evars_of_term sigma term in
    Feedback.msg_notice (str "Evars in term: "
      ++ prlist_with_sep (fun () -> str ", ") Evar.print (Evar.Set.elements evars))

let evar_list_from_term (term : Evd.econstr) :
  Evar.t list tactic =
  tclEVARMAP >>= fun sigma -> tclUNIT @@
    let evars = Evarutil.undefined_evars_of_term sigma term in
    List.filter (is_internal_hole sigma) (Evar.Set.elements evars)

let make_new_evar_tac (input : Evar.t) : unit tactic =
  Proofview.Goal.enter begin fun gl ->
    let gl_sigma = Proofview.Goal.sigma gl in
    let found_evar = (Evd.find gl_sigma input) in
    let desired_type = Evd.evar_concl found_evar in
    Evar_tactics.let_evar (Names.Name.mk_name (Names.Id.of_string "name_of_variable"))
      desired_type
  end

let make_evar_from_constr (input : string) : unit tactic =
  let src = (Loc.tag Evar_kinds.GoalEvar) in
  Proofview.Goal.enter begin fun gl ->
    let gl_sigma = Proofview.Goal.sigma gl in
    let env = Proofview.Goal.env gl in
    let concl = Proofview.Goal.concl gl in
    let state_store = Proofview.Goal.state gl in 
    (* let (l, k) = (Evd.evar_source (Evd.find gl_sigma (Proofview.Goal.goal gl))) in*)
    Refine.refine ~typecheck:true begin function sigma ->
      let sigma, t = Evarutil.new_evar ~src ~naming:(Namegen.IntroFresh (Names.Id.of_string input)) env sigma concl in
      (sigma, t)
    end
      (* Tacticals.tclTHEN (Proofview.Unsafe.tclEVARS sigma)
      (Tactics.pose_tac (Name.mk_name (Names.Id.of_string "my_variable_name")) t)*)
  end

let print_number_of_goals : unit tactic =
  numgoals >>= fun i ->
    tclUNIT @@ Feedback.msg_notice (str "Number of goals: "++ Pp.int i)
  (* tclTHEN (make_evar_from_constr "hey")
  (tclUNIT @@ Feedback.msg_notice (str "tried to find num goals"))*)

let print_number_of_goals_on_shelf : unit tactic =
  Proofview.Unsafe.tclGETSHELF >>= fun ls ->
    tclUNIT @@ Feedback.msg_notice (str "Number of goals on shelf: "++ Pp.int (List.length ls))

let focus_on_first : unit tactic =
  tclFOCUS 1 1 (make_evar_from_constr "hey")

let try_to_get_proofview =
  Proofview.Goal.enter begin fun gl ->
    let gl_sigma = Proofview.Goal.sigma gl in
    let env = Proofview.Goal.env gl in
    (* for testing purposes only *)
    let gl_ev = Proofview.Goal.goal gl in
    let _, pv = Proofview.init gl_sigma [] in
    let pv = (Proofview.unshelve [gl_ev] pv) in
    let _, _ , _, _ = Proofview.apply 
      ~name:(Names.Id.of_string "test_name") ~poly:true env
      (print_number_of_goals <*> print_number_of_goals_on_shelf
       <*> focus_on_first) pv in
    tclUNIT @@ (Feedback.msg_notice (str "try to get proofview"))
  end

let update_proofview =
  Proofview_monad.Pv.get  

open Pp
open Util
open Proof
open Proofview_monad
open Context.Named.Declaration

let () = define0 "print_evars_external" @@ print_evars

let () =
  define1 "print_evar_info_external" evar print_evar_info

let () =
  define1 "warn_external" pp @@ 
    fun input ->
      warn input >>= fun () -> tclUNIT @@ of_unit ()

let () =
  define1 "find_evars_in_term_external" constr find_evars_in_term

let () =
  define1 "make_new_evar_external" evar @@
    fun input -> make_new_evar_tac input >>= fun () -> tclUNIT @@ of_unit ()

let () =
  define1 "make_evar_from_constr_external" string @@
    fun input -> make_evar_from_constr input >>= fun () -> tclUNIT @@ of_unit ()

let () =
  define0 "try_to_get_proofview_external" @@
    let f = (fun () -> (tclUNIT @@ of_unit ())) in
    try_to_get_proofview >>= f

let () =
  define0 "focus_on_first_external" @@
    let f = (fun () -> (tclUNIT @@ of_unit ())) in
    focus_on_first >>= f

let () =
  define1 "evar_list_from_term_external" constr @@
    fun term ->
      evar_list_from_term term >>= 
      fun evars -> tclUNIT @@ (of_list of_evar evars)
