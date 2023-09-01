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

Require Import Ltac2.Ltac2.
Require Import Ltac2.Message.
Ltac2 Type exn ::=  [ Inner
                    | FailedToUse (constr)
                    | FailedToProve (constr) ].

Require Import Waterproof.

Require Import Ltac2.Bool.
Require Import Ltac2.Init.

Require Import Chains.Inequalities.

Local Ltac2 Type database_type_ffi.

Local Ltac2 @ external database_type_main: unit -> database_type_ffi := "coq-waterproof" "database_type_main".
Local Ltac2 @ external database_type_decidability: unit -> database_type_ffi := "coq-waterproof" "database_type_decidability".
Local Ltac2 @ external database_type_shorten: unit -> database_type_ffi := "coq-waterproof" "database_type_shorten".

Local Ltac2 @ external waterprove_ffi: int -> bool -> (unit -> constr) list -> database_type_ffi -> unit := "coq-waterproof" "waterprove".
Local Ltac2 @ external rwaterprove_ffi: int -> bool -> (unit -> constr) list -> database_type_ffi -> constr list -> constr list -> unit := "coq-waterproof" "rwaterprove".

Ltac2 Type database_type := [ Main | Decidability | Shorten ].

Local Ltac2 database_type_to_ffi (db_type: database_type): database_type_ffi :=
  match db_type with
    | Main => database_type_main ()
    | Decidability => database_type_decidability ()
    | Shorten => database_type_shorten ()
  end.

Local Ltac2 contains_shielded_pattern (): bool :=
  lazy_match! goal with
    | [ |- forall _, _ ] => true
    | [ |- exists _, _ ] => true
    | [ |- _ /\ _] => true
    | [ |- _ \/ _] => true
    | [ |- _] => false
  end.

(** Internal versions of [waterprove] and [rwaterprove]. *)
Local Ltac2 _waterprove (depth: int) (shield: bool) (lems: (unit -> constr) list) (db_type: database_type): unit  :=
  waterprove_ffi depth (shield && contains_shielded_pattern ()) lems (database_type_to_ffi db_type).

Local Ltac2 _risky_rwaterprove (depth: int) (shield: bool) (lems: (unit -> constr) list) (db_type: database_type) (must : constr list) (forbidden : constr list) : unit  :=
  rwaterprove_ffi depth (shield && contains_shielded_pattern ()) lems (database_type_to_ffi db_type) must forbidden.
  

(** Checks whether [x] is in the current list of hypotheses *)
(* TODO: there could be a better way with [Control.hyps], but this seems to work. *)
Local Ltac2 in_hypotheses (x : constr) :=
  match! goal with
  | [ h_id : _ |- _ ] =>
    (* check if xtr_lemma matches h *)
    let h := Control.hyp h_id in
    match Constr.equal x h with
    | false => Control.zero Inner
    | true => true
    end
  | [ |- _ ] => false
  end.

Local Ltac2 _rwaterprove (depth: int) (shield: bool) (db_type: database_type) 
  (xtr_lemma : constr) : unit :=
  (* workaround for anomalies and troubles with proof finding
     when additional extra lemma is one of the hypotheses *)
  (* Anonalies occur when 
      1. the goal can be solved and [xtr_lemma] is the most recent (and second to most recent?) 
        hypothesis added
      2. the goal cannot be solved and [xtr_lemma] is a hypothesis *)
  match in_hypotheses xtr_lemma with
  | false =>
    (* xtr_lemma is not one of the hypotheses, so we can use rwaterprove without risking anomalies. *)
    _risky_rwaterprove depth shield [fun () => xtr_lemma] db_type [xtr_lemma] []
  | true =>
    _waterprove depth shield [] Main
  end.


(** Subroutine to solve conjunction of statements piece by piece.
  Throws [FailedToProve] error with statement that could not be proven. *)
(* Assumes goal is of the form (g1 /\ ... /\ gn). *)
Local Ltac2 rec waterprove_iterate_conj (depth: int) (shield: bool)
 (db_type: database_type) (xtr_lemma : constr option) :=
  (* accepts optional extra lemma since it can be called by restricted version 
    [rwaterprove_iterate_conj] when extra lemma is no longer required but still available *)
  let list_lemmas := 
    match xtr_lemma with
    | None => []
    | Some lem => [fun () => lem]
    end
  in
  lazy_match! goal with
  (* recursion step *)
  | [ |- ?g1 /\ ?remainder ] =>
    split;
    (* Attempt to prove 1st goal *)
    match Control.case (fun () => Control.focus 1 1 (fun () =>
      _waterprove depth shield list_lemmas db_type))
    with
    | Val _ => waterprove_iterate_conj depth shield db_type xtr_lemma
    | Err exn => Control.zero (FailedToProve g1)
    end
  (* base case *)
  | [ |- _ ] =>
    (* Prove remaining goal. *)
    match Control.case (fun () => 
      _waterprove depth shield list_lemmas db_type)
    with
    | Val _ => ()
    | Err exn => Control.zero (FailedToProve (Control.goal ()))
    end
  end.

(** Subroutine to solve conjunction of statements piece by piece
  using an extra lemma which has to be used.
  Throws [FailedToProve] error with statement that could not be proven.
  Throws [FailedToUse] error if no proof of the statements used the extra lemma. *)
(* Assumes goal is of the form (g1 /\ ... /\ gn). *)
Local Ltac2 rec rwaterprove_iterate_conj (depth: int) (shield: bool)
 (db_type: database_type) (xtr_lemma : constr) :=
  lazy_match! goal with
  (* recursion step *)
  | [ |- ?g1 /\ _ ] =>
    split;
    (* Attempt to prove 1st goal with extra lemma. *)
    match Control.case (fun () => Control.focus 1 1 (fun () =>
      _rwaterprove depth shield db_type xtr_lemma))
    with
    | Val _ => 
      (* succesfully used lemma; prove remaining goals, but without restriction. *)
      waterprove_iterate_conj depth shield db_type (Some xtr_lemma)
    | Err exn => 
      (* failed, could be due to restriction; try to prove without. *)
      match Control.case (fun () => Control.focus 1 1 (fun () =>
        _waterprove depth shield [] db_type))
      with
      | Val _ => 
        (* succesful. prove remaining statements with restriction. *)
        rwaterprove_iterate_conj depth shield db_type xtr_lemma
      | Err exn => Control.zero (FailedToProve g1)
      end
    end
  (* base case *)
  | [ |- _ ] =>
    (* Prove remaining goal with restriction. *)
    match Control.case (fun () =>
      _rwaterprove depth shield db_type xtr_lemma)
    with
    | Val _ => ()
    | Err exn => (* failed, if due to restricition, give feedback *)
      (* check if it would work without lemma *)
      match Control.case (fun () =>
        _waterprove depth shield [] db_type)
      with
      | Err exn => Control.zero (FailedToProve (Control.goal ()))
      | Val _ => (* problem is the extra lemma *)
        Control.zero (FailedToUse xtr_lemma)
      end
    end
  end.


(** External versions of (restricted) automation. 
  (In)equality chains are attempted piece by piece. *)

Lemma _and_assoc1 (A B C : Prop) : A /\ B /\ C -> (A /\ B) /\ C.
Proof. apply and_assoc. Qed.

(**  Attempts to prove current goal. 
  Throws [FailedToProve] error with statement that could not be proven.
  (In)equality chains are attempted piece by piece.
*)
Ltac2 waterprove (depth: int) (shield: bool) (db_type: database_type) :=
  lazy_match! goal with
  (* prove (in)equality chain piece by piece to give better feedback *)
  | [ |- total_statement _ ] =>
    cbn; repeat (apply _and_assoc1); (* get chain into shape: g1 /\ ... /\ gn *)
    waterprove_iterate_conj depth shield db_type None
  (* regular proof attempt *)
  | [ |- _] =>
    match Control.case (fun () =>
      _waterprove depth shield [] db_type)
    with
    | Val _ => ()
    | Err exn => Control.zero (FailedToProve (Control.goal ()))
    end
  end.

(**  Attempts to prove current goal. 
  Throws [FailedToProve] error with statement that could not be proven.
  Throws [FailedToUse] error with [xtr_lemma] if no proof could be found
    that uses it.
  (In)equality chains are attempted piece by piece.
*)
Ltac2 rwaterprove (depth: int) (shield: bool) (db_type: database_type) (xtr_lemma : constr) :=
  lazy_match! goal with
  (* prove (in)equality chain piece by piece to give better feedback *)
  | [ |- total_statement _ ] =>
    cbn; repeat (apply _and_assoc1); (* get chain into shape: g1 /\ ... /\ gn *)
    rwaterprove_iterate_conj depth shield db_type xtr_lemma
  (* regular proof attempt *)
  | [ |- _] =>
    (* Prove goal with restriction. *)
    match Control.case (fun () =>
      _rwaterprove depth shield db_type xtr_lemma)
    with
    | Val _ => ()
    | Err exn => (* failed, if due to restricition, give feedback *)
      (* check if it would work without lemma *)
      match Control.case (fun () =>
        _waterprove depth shield [] db_type)
      with
      | Err exn => Control.zero (FailedToProve (Control.goal ()))
      | Val _ => (* problem is the extra lemma *)
        Control.zero (FailedToUse xtr_lemma)
      end
    end
  end.