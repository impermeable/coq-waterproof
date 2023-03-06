(** * [choose_such_that.v]
Author: 
    - Cosmin Manea (1298542)
Creation date: 30 May 2021

Various tactics for instantiating a variable according to a specific rule given from a
previously known result.
--------------------------------------------------------------------------------

This file is part of Waterproof-lib.

Waterproof-lib is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

Waterproof-lib is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with Waterproof-lib.  If not, see <https://www.gnu.org/licenses/>.
*)


From Ltac2 Require Import Ltac2.
From Ltac2 Require Option.


Require Import Waterproof.message.

Ltac2 Type exn ::= [ ChooseSuchThatError(message) ].

Require Import Waterproof.auxiliary.
Require Import Waterproof.tactics.goal_wrappers.


Local Ltac2 mismatch_pred_existential_message (s : ident) (v : ident) :=
  Message.concat (Message.concat
    (Message.concat (of_string "Claimed property of ") (of_ident s))
    (Message.concat (of_string " does not match ‘there exists’-statement (") (of_ident v))) (of_string ").").


(** * choose_such_that
    Chooses a variable according to a particular hypothesis and labels the remaining parts 
    of the definition.

    Arguments:
        - [s: ident], the name of the variable to be chosen.
        - [v: ident], the hypothesis used.
        - [pred_u: constr], predicate that should hold for [s] 
                            and [v]'s type should match (ex [pred_u]) or (sig [pred_u]).
        - [u: ident option], optional name of property that [s] is to satisfy.
    Does:
        - Destructs the constr [v] under the names [s] (and [u]).
        - Copies the hypothesis [v] to a new hypothesis also called [v],
            hence the hypothesis is preserved despite its destruction.

    Raises exceptions:
        - [ChooseSuchThatError], if [v]'s type does not match (ex [pred_u]) or (sig [pred_u]).
*)

Ltac2 choose_such_that (s:ident) (v:ident) (pred_u:constr) (u:ident option)
 := let v_val := Control.hyp v in
    let copy_id := Fresh.in_goal @copy in
    (* Create identifier if u is not specified. *)
    let uu := match u with
              | None   => Fresh.in_goal @__wp__h
              | Some u => u
              end
    in
    match Control.case 
    (fun () =>
      (* Copy v, also count as check that v can be converted to (ex pred_u) *)
      assert (ex  $pred_u) as $copy_id;
      Control.focus 1 1 (fun () => exact $v_val)
    ) with
    | Val _ =>
      (* ~continue with (v = ex  pred_u) case~ *)
      (* Destruct v *)
      destruct $v_val as [$s $uu];
      (* Copy the copy, but with name v*)
      assert (ex  $pred_u) as $v;
      Control.focus 1 1 (fun () => 
      let copy_val := Control.hyp copy_id in exact $copy_val);
      (* Destroy copy *)
      clear $copy_id
    | Err e =>
      Control.plus
      (fun () =>
        (* Copy v, also count as check that v can be converted to (sig pred_u) *)
        assert (sig $pred_u) as $copy_id;
        Control.focus 1 1 (fun () => exact $v_val)
      )
      (fun e =>
        Control.zero (ChooseSuchThatError (mismatch_pred_existential_message s v))
      );
      (* ~continue with (v = sig pred_u) case~ *)
      (* Destruct v *)
      destruct $v_val as [$s $uu];
      (* Copy the copy, but with name v*)
      assert (sig $pred_u) as $v;
      Control.focus 1 1 (fun () => 
        let copy_val := Control.hyp copy_id in exact $copy_val);
      (* Destroy copy *)
      clear $copy_id
    end.


(* Desired syntax:
    Choose x according to (i), so for x : A it holds that (P x) (ii). *)

Notation "'for' x : A 'it' 'holds' 'that' p" := (fun x : A => p) (at level 1, x name, only parsing).

Ltac2 Notation "Obtain" s(ident) "according" "to" "("v(ident)")" "," "so" pred_u(constr) u(opt(seq("(", ident, ")")))
 := panic_if_goal_wrapped ();
    choose_such_that s v pred_u u.
