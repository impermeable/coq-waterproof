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

open Ltac2_plugin.Tac2entries
open Ltac2_plugin.Tac2expr
open Names

module StringMap = Map.Make(String)

let wp_unfold_map = Summary.ref ~name:"wp_unfold_map" StringMap.empty

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

let add_to_unfold_map (s : string) (id : GlobRef.t) : unit =
  Lib.add_leaf (declare_unfold_map (StringMap.add s id !wp_unfold_map))

let extract_def (s : string) : GlobRef.t option =
  StringMap.find_opt s !wp_unfold_map

let register_unfold (toks : string list) (id : GlobRef.t) : notation_interpretation_data =
  let concatenated_str = (String.concat " " toks) in
  add_to_unfold_map concatenated_str id;
  let atom_str = CTacAtm (AtmStr concatenated_str) in
  let sexpr_seq = List.map (fun s -> SexprStr (CAst.make s)) toks in
  register_notation [] sexpr_seq (Some 1) (CAst.make atom_str)
