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

open Proof
open Proof_bullet

(** The majority of the code below is copied and adapted directly from
the source code of the Rocq theorem prover itself, namely from Proof_bullet.ml. *)

(** Preparatory definitions that are useful for both defined modes. *)

let bullet_eq b1 b2 = match b1, b2 with
| Dash n1, Dash n2 -> n1 = n2
| Star n1, Star n2 -> n1 = n2
| Plus n1, Plus n2 -> n1 = n2
| _ -> false

let pr_bullet b =
  match b with
  | Dash n -> Pp.(str (String.make n '-'))
  | Star n -> Pp.(str (String.make n '*'))
  | Plus n -> Pp.(str (String.make n '+'))

type suggestion =
  | Suggest of t (* this bullet is mandatory here *)
  | Unfinished of t (* no mandatory bullet here, but this bullet is unfinished *)
  | NoBulletInUse (* No mandatory bullet (or brace) here, no bullet pending,
               some focused goals exists. *)
  | NeedClosingBrace (* Some unfocussed goal exists "{" needed to focus them *)
  | ProofFinished (* No more goal anywhere *)

let suggest_on_solved_goal sugg =
  match sugg with
  | NeedClosingBrace -> Pp.(str"Try closing this subproof by typing a space and curly brace \" }\".")
  | NoBulletInUse -> Pp.mt ()
  | ProofFinished -> Pp.mt ()
  | Suggest b -> Pp.(str"Write a bullet " ++ pr_bullet b ++ str" to embark on the next subproof.")
  | Unfinished b -> Pp.(str"The current subproof with bullet " ++ pr_bullet b ++ str" is unfinished.")

(* give always a message. *)
let suggest_on_error sugg =
  match sugg with
  | NeedClosingBrace -> Pp.(str"Try closing this subproof by typing a space and curly brace \" }\".")
  | NoBulletInUse -> assert false (* This should never raise an error. *)
  | ProofFinished -> Pp.(str"No more goals.")
  | Suggest b -> Pp.(str"Write a bullet " ++ pr_bullet b ++ str" to embark on the next subproof.")
  | Unfinished b -> Pp.(str"Current bullet " ++ pr_bullet b ++ str" is not finished.")

let bullet_kind = (new_focus_kind () : t list focus_kind)
let bullet_cond = done_cond ~loose_end:true bullet_kind

let get_bullets pr =
  if is_last_focus bullet_kind pr then
    get_at_focus bullet_kind pr
  else
    []

let has_bullet bul pr =
  let rec has_bullet = function
    | b'::_ when bullet_eq bul b' -> true
    | _::l -> has_bullet l
    | [] -> false
  in
  has_bullet (get_bullets pr)

(* pop a bullet from proof [pr]. There should be at least one
    bullet in use. If pop impossible (pending proofs on this level
    of bullet or higher) then raise [Proof.CannotUnfocusThisWay]. *)
let pop pr =
  match get_bullets pr with
  | b::_ -> Some (unfocus bullet_kind pr (), b)
  | _ -> None

let push (b:t) pr =
  focus bullet_cond (b::get_bullets pr) 1 pr

let suggest_bullet (prf : Proof.t): suggestion =
  if is_done prf then ProofFinished
  else if not (no_focused_goal prf)
  then (* No suggestion if a bullet is not mandatory, look for an unfinished bullet *)
    match get_bullets prf with
    | b::_ -> Unfinished b
    | _ -> NoBulletInUse
  else (* There is no goal under focus but some are unfocussed,
          let us look at the bullet needed. *)
    let rec loop prf =
      match pop prf with
      | Some (prf, b) ->
        (* pop went well, this means that there are no more goals
          *under this* bullet b, see if a new b can be pushed. *)
        begin
          try ignore (push b prf); Suggest b
          with e when CErrors.noncritical e ->
            (* b could not be pushed, so we must look for a outer bullet *)
            loop prf
        end
      | None ->
        (* No pop was possible, but there are still
            subgoals somewhere: there must be a "}" to use. *)
        NeedClosingBrace
    in
    loop prf

(** Definitions for the bullet behavior "Waterproof Strict Subproofs".
This is the same as the ordinary "Strict Subproofs" bullet behavior,
except that the suggestions and error messages are slightly different. *)
module Strict = struct
  exception FailedBullet of t * suggestion

  let _ =
    CErrors.register_handler
      (function
      | FailedBullet (b,sugg) ->
        let prefix = Pp.(str"Wrong bullet " ++ pr_bullet b ++ str": ") in
        Some Pp.(str "[Focus]" ++ spc () ++ prefix ++ suggest_on_error sugg)
      | _ -> None)

  let rec pop_until (prf : Proof.t) bul : Proof.t =
    let prf', b = Option.get (pop prf) in
    if bullet_eq bul b then prf'
    else pop_until prf' bul

  let put p bul =
    try
      if not (has_bullet bul p) then
        (* bullet is not in use, so pushing it is always ok unless
           no goal under focus. *)
        push bul p
      else
        match suggest_bullet p with
        | Suggest suggested_bullet when bullet_eq bul suggested_bullet
            -> (* suggested_bullet is mandatory and you gave the right one *)
          let p' = pop_until p bul in
          push bul p'
      (* the bullet you gave is in use but not the right one *)
        | sugg -> raise (FailedBullet (bul,sugg))
    with NoSuchGoals _ -> (* push went bad *)
      raise (FailedBullet (bul,suggest_bullet p))

  let strict = {
    name = "Waterproof Strict Subproofs";
    put = put;
    suggest = (fun prf -> suggest_on_solved_goal (suggest_bullet prf))

  }
  let _ = register_behavior strict
end

(** Definitions for the bullet behavior "Waterproof Relaxed Subproofs."
A bullet point will unfocus all finished subproofs, and will focus a new subproof. *)
module Relaxed = struct
  (** Unfocus as many proofs as possible: this should correspond to unfocusing
  all subproofs that are finished. *)
  let rec pop_until (prf : Proof.t) : Proof.t =
    try
      let prf', b = Option.get (pop prf) in
      pop_until prf'
    with e when CErrors.noncritical e ->
      prf

  (** The intention here is to unfocus all finished subproofs, and then
    start a new bullet. *)
  let put p bul =
    let prf = pop_until p in
    push bul prf

  let wp_relaxed_bullets = {
    name = "Waterproof Relaxed Subproofs";
    put = put;
    suggest = (fun prf -> suggest_on_solved_goal (suggest_bullet prf))

  }
  let _ = register_behavior wp_relaxed_bullets
end
