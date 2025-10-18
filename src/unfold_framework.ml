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

(**
In this module we keep two tables:
- [wp_unfold_map] a map from strings to global references, that is used to keep track of the
introduced notations, and the global reference they are associated with
- [wp_unfold_tbl] a table from global references to unfold actions, that can later be used
  by the unfold framework. The unfold actions can be of three types:
    - unfold the definition associated to the global reference
    - apply a bi-implication
    - rewrite an equality
*)

open Ltac2_plugin.Tac2entries
open Ltac2_plugin.Tac2expr
open Names

module StringMap = Map.Make(String)

(** A type to represent the different unfold actions, and the data they need. *)
type unfold_action =
  | Unfold of GlobRef.t
  | Apply of EConstr.constr
  | Rewrite of EConstr.constr

(** The map that associate notation strings to references *)
  let wp_unfold_map = Summary.ref ~name:"wp_unfold_map" StringMap.empty

(** The table that associates global references to unfold actions *)
let wp_unfold_tbl : (GlobRef.t, unfold_action) Hashtbl.t ref = Summary.ref ~name:"wp_unfold_tbl" (Hashtbl.create 60)

(** The following constructions are necessary to ensure persistence of the tables.. *)

let cache_unfold_map mp =
  wp_unfold_map := mp

let declare_unfold_map =
  let open Libobject in
  declare_object
    {
      (default_object "WP_UNFOLD_MAP") with
      cache_function = cache_unfold_map;
      load_function = (fun _ -> cache_unfold_map);
      classify_function = (fun _ -> Keep);
    }

let cache_unfold_tbl tbl =
  wp_unfold_tbl := tbl

let declare_unfold_tbl =
  let open Libobject in
  declare_object
    {
      (default_object "WP_UNFOLD_TBL") with
      cache_function = cache_unfold_tbl;
      load_function = (fun _ -> cache_unfold_tbl);
      classify_function = (fun _ -> Keep);
    }

let add_to_unfold_map (s : string) (id : GlobRef.t) : unit =
  Lib.add_leaf (declare_unfold_map (StringMap.add s id !wp_unfold_map))

let add_to_unfold_tbl (id : GlobRef.t) (ua : unfold_action) : unit =
  Hashtbl.add !wp_unfold_tbl id ua;
  Lib.add_leaf (declare_unfold_tbl !wp_unfold_tbl)

let extract_def (s : string) : GlobRef.t option =
  StringMap.find_opt s !wp_unfold_map

(**
    Registers a new unfold notation in the notation table.

    Arguments:
    - [toks]: the list of string tokens that compose the notation
    - [id]: the global reference to associate the unfold action to

    Returns:
    - the notation interpretation data created
*)
let register_unfold (toks : string list) (id : GlobRef.t) : notation_interpretation_data =
  let concatenated_str = (String.concat " " toks) in
  let atom_str = CTacAtm (AtmStr concatenated_str) in
  let sexpr_seq = List.map (fun s -> SexprStr (CAst.make s)) toks in
  add_to_unfold_map concatenated_str id;
  register_notation [] sexpr_seq (Some 1) (CAst.make atom_str)

(** A type that represents the datastructure that can be added
    to the unfold table. When it is added, it will be converted
    to an unfold action.
*)
type unfold_entry =
  | Unfold_entry
  | Apply_entry of Constrexpr.constr_expr
  | Rewrite_entry of Constrexpr.constr_expr

(** Registers a new entry in the table that stores a list of
    unfold actions associated to a reference.

    In this step, the [Constrexpr.constr_expr] is interpreted
    into an [EConstr.constr] to be stored in the unfold table.

    Arguments:
    - [id]: the global reference to associate the unfold action to
    - [ue]: the unfold action to register
*)
let register_unfold_entry (id : GlobRef.t) (ue : unfold_entry) : unit =
  let f (e : Constrexpr.constr_expr) =
    let env = Global.env () in
    let sigma = Evd.from_env env in
    let (constr_e, _) = Constrintern.interp_constr env sigma e in
    constr_e in
  match ue with
  | Unfold_entry -> add_to_unfold_tbl id (Unfold id)
  | Apply_entry e ->
      add_to_unfold_tbl id (Apply (f e))
  | Rewrite_entry e ->
      add_to_unfold_tbl id (Rewrite (f e))

let get_all_references () : GlobRef.t list =
  let lst = !wp_unfold_tbl |> Hashtbl.to_seq_keys |> List.of_seq in
  (* Remove duplicates *)
  let tbl = Hashtbl.create (List.length lst) in
  List.iter (fun x -> Hashtbl.replace tbl x ()) lst;
  Hashtbl.fold (fun key _ acc -> key :: acc) tbl []

let find_unfold_actions_by_ref (r : GlobRef.t) : unfold_action list =
  Hashtbl.find_all !wp_unfold_tbl r

let find_unfold_actions_by_str (s : string) : unfold_action list =
  match extract_def s with
  | Some r -> find_unfold_actions_by_ref r
  | None -> []
