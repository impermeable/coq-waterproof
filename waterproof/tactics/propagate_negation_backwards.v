(** * [propagate_negation_backwards.v]
Authors: 
    - Jelle Wemmenhove
Creation date: 2 Nov 2021

TODO: description

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
From Ltac2 Require Import Message.



Require Import Waterproof.auxiliary.
Require Import Classical_Prop.
Require Import Classical_Pred_Type.

Ltac2 Type exn ::= [ PropagateNegationError(string) | PassConstr(constr)].


(** Required lemmas.
    Perhaps these can be found in the standard Coq library,
    I did not look thoroughly. *)
Lemma and_to_imply : forall P Q : Prop, ~ (P /\ Q) -> P -> ~ Q.
Proof. intros P Q h p q. exact (h (conj p q)). Qed.

(* The next ones I have named with 'functoriality', but full functoriality
   would also require the identity arrow to be preserved. *)
Lemma functorality_disj {A B C : Prop} :
  (B -> C) -> (A \/ B) -> (A \/ C).
Proof. intros h ab. destruct ab as [a | b]. left; exact a. right; exact (h b). Qed.

Lemma functorality_conj {A B C : Prop} :
  (B -> C) -> (A /\ B) -> (A /\ C).
Proof. intros h ab. destruct ab as [a b]. exact (conj a (h b)). Qed.

Lemma functorality_impl {A B C : Prop} :
  (B -> C) -> (A -> B) -> (A -> C).
Proof. intros h g a. exact (h (g a)). Qed.

Lemma functorality_forall {A : Type} {P Q : A -> Prop} : 
  (forall x, P x -> Q x) -> (forall x, P x) -> (forall x, Q x).
Proof.
  intros H HP x. exact ((H x) (HP x)).
Qed.

Lemma functorality_exists {A : Type} {P Q : A -> Prop} : 
  (forall x, P x -> Q x) -> (exists x, P x) -> (exists x, Q x).
Proof.
  intros H HP. destruct HP as [x Hx]. exists x. exact (H x Hx).
Qed.


(** 'transparent assert'-hack. 
    The Ltac1 tactic 'transparent assert' is taken from the HoTT library.
    In order to make it work in Ltac2, we need a hack that makes 'transparent assert'
    accepts the ident 'name' parameter as a constr, as Ltac1.of_ident is not yet implemented.
    (This is strange as it shown on 'https://coq.inria.fr/library/Ltac2.Ltac1.html' .) *)
Local Ltac transparent_assert name type := 
  simple refine (let __transparent_assert_hypothesis := (_ : type) in _);
    [
    | (
      let H := match goal with H := _ |- _ => constr:(H) end in
      rename H into name) ].

Local Ltac transparent_assert_constr name_constr type :=
  lazymatch name_constr with
  | fun name => _ => transparent_assert name type
  end.

Local Ltac2 ident_to_constr (i:ident) :=
  constr:(ltac2:(clear; intros $i; exact tt) : unit -> unit).


(** 'fa'-hack.
    Invented to obtain the predicate (fun x => P x) from a forall statement (forall x, P x). 
    How it works: 
    - Create a new type 'fa' with the predicate as parameter,
      defined as the forall statement.
    - Proof that these are in fact equal.
    - Use the above proof to rewrite a forall statement in a goal
      as a 'fa' type. Then match on this goal to obtain the predicate.
*)

Definition fa {A : Type} (P : A -> Prop) := forall x, P x.
Lemma fa_eq_forall {A : Type} {P : A -> Prop} : fa P = forall x, P x.
Proof. reflexivity. Qed.

(* (* Tests for 'fa'-hack. *)
Goal forall x : nat, exists y : nat, forall z : nat, ~ P x y z.
Proof.
  rewrite <- fa_eq_forall.
Abort.

Goal {G : Prop | G -> exists t : nat, forall x : nat, exists y : nat, forall z : nat, ~ P x y z}.
  rewrite <- fa_eq_forall.
Abort.
*)

(** 'notpred'-hack.
    Invented to obtain the predicate (fun x => P x) from a predicate with negation (fun x => ~ P x). 
    How it works: 
    - Create a new type 'notpred' with the predicate as parameter,
      defined as the predicate with negation.
    - Proof that these are in fact equal.
    - Use the above proof to rewrite a predicate with negation in a goal
      as a 'notpred' type. Then match on this goal to obtain the predicate.
*)

Definition notpred {A : Type} (P : A -> Prop) := fun x => ~ P x.
Lemma notpred_eq_prednot {A : Type} {P : A -> Prop} : notpred P = fun x => ~ P x.
Proof. reflexivity. Qed.

(* (* Tests for 'notpred'-hack. *)
Goal forall x : nat, ~(0 = 1).
  rewrite <- fa_eq_forall.
  rewrite <- notpred_eq_prednot.
Abort.

Goal {G : Prop | G -> forall z : nat, ~ P 0 0 z}.
  rewrite <- fa_eq_forall.
  rewrite <- notpred_eq_prednot.
Abort.
*)


(** 'fa' and 'notpred'-hack subroutines.
     Used to get a predicate from a constr [t] that has the form of a 
      forall statement with negation, exists statement with negation,
      or forall statemen.  *)

Local Ltac2 get_allnot_pred (t : constr) :=
  (* Assumption: [t] is of the form (forall x, ~ P x) *)
  let attempt () := assert $t; 
                    Control.focus 1 1 (fun () => 
                      rewrite <- fa_eq_forall;
                      rewrite <- notpred_eq_prednot;
                      lazy_match! goal with 
                      | [ |- fa (notpred ?p) ] => Control.zero (PassConstr p)
                      end
                    )
  in
  match Control.case attempt with
  | Err exn => match exn with 
               | PassConstr exn => exn
               | exn => Control.zero exn (* Should not happen. *)
               end
  | Val _ => constr:(0=1) (* Should not happen. *)
  end.

Local Ltac2 get_exnot_pred (t : constr) :=
  (* Assumption: [t] is of the form (exists x, ~ P x) *)
  let attempt () := assert $t; 
                    Control.focus 1 1 (fun () => 
                      rewrite <- notpred_eq_prednot;
                      lazy_match! goal with 
                      | [ |- ex (notpred ?p) ] => Control.zero (PassConstr p)
                      end
                    )
  in
  match Control.case attempt with
  | Err exn => match exn with 
               | PassConstr exn => exn
               | exn => Control.zero exn (* Should not happen. *)
               end
  | Val _ => constr:(0=1) (* Should not happen. *)
  end.

Local Ltac2 get_all_pred (t : constr) :=
  (* Assumption: [t] is of the form (forall x, P x) *)
  let attempt () := assert $t; 
                    Control.focus 1 1 (fun () => 
                      rewrite <- fa_eq_forall;
                      lazy_match! goal with 
                      | [ |- fa ?p ] => Control.zero (PassConstr p)
                      end
                    )
  in
  match Control.case attempt with
  | Err exn => match exn with 
               | PassConstr exn => exn
               | exn => Control.zero exn (* Should not happen. *)
               end
  | Val _ => constr:(0=1) (* Should not happen. *)
  end.


(** Recursive part of the tactic: 
    Recursively tries to find a proposition [new_g] such that [new_g] -> [g].
    For example, if the [g] is (forall x, exists y, ~ P x y),
      we first try to find for all x a proposition [new_g_x] such that [new_g_x] -> (exists y, ~ P x y),
      we then use this to solve the original task:
        [new_g] := (forall x, [new_g_x]) and hence [new_g] -> [g].
    Warning: will mess up variable names!!!
  *)
Local Ltac2 rec iterate () :=
  (*Assumption: goal to be of the form: (sig (fun new_g : Prop => new_g -> g) *)
  lazy_match! goal with
  (* Base cases *)
  | [ |- { _ | _ -> not ?p \/ not ?q}] =>
      (* g is of the form (~ P \/ ~ Q) *)
      exists (~ ($p /\ $q)); exact (not_and_or $p $q)
  | [ |- { _ | _ -> not ?p /\ not ?q}] =>
      (* g is of the form (~ P /\ ~ Q) *)
      exists (~ ($p \/ $q)); exact (not_or_and $p $q)
  | [ |- { _ | _ ->     ?p /\ not ?q}] =>
      (* g is of the form (  P /\ ~ Q) *)
      exists (~ ($p -> $q)); exact (imply_to_and $p $q)
  | [ |- { _ | _ ->     ?p -> not ?q}] =>
      (* g is of the form (  P -> ~ Q) *)
      exists (~ ($p /\ $q)); exact (and_to_imply $p $q)
  | [ |- { _ | _ -> forall _, not _ }] => 
      (* g is of form (forall x, ~ P x) *)
      lazy_match! goal with 
      | [ |- { _ | _ -> ?g }] =>
          let p := get_allnot_pred g in
          exists (~ (ex $p)); exact (not_ex_all_not _ $p)
      end
  | [ |- { _ | _ -> exists _, not _ }] =>
      (* g is of form (exists x, ~ P x) *)
      lazy_match! goal with 
      | [ |- { _ | _ -> ?g }] =>
          let p := get_exnot_pred g in
          exists (~ (forall x, $p x)); exact (not_all_ex_not _ $p)
      end
  (* Cases that require iteration. *)
  | [ |- { _ | _ -> ?p \/ ?q}] =>
      (* g is of the form (P \/ Q) *)
      let h_id := Fresh.in_goal @h in
      enough (sig (fun g : Prop => g -> $q)) as $h_id;
      Control.focus 1 1 (fun () =>
        let h := Control.hyp h_id in
        exists ($p \/ proj1_sig $h); exact (functorality_disj (proj2_sig $h))
      );
      iterate ()
  | [ |- { _ | _ -> ?p /\ ?q}] =>
      (* g is of the form (P /\ Q) *)
      let h_id := Fresh.in_goal @h in
      enough (sig (fun g : Prop => g -> $q)) as $h_id;
      Control.focus 1 1 (fun () =>
        let h := Control.hyp h_id in
        exists ($p /\ proj1_sig $h); exact (functorality_conj (proj2_sig $h))
      );
      iterate ()
  | [ |- { _ | _ -> ?p -> ?q}] =>
      (* g is of the form (P -> Q) *)
      let h_id := Fresh.in_goal @h in
      enough (sig (fun g : Prop => g -> $q)) as $h_id;
      Control.focus 1 1 (fun () =>
        let h := Control.hyp h_id in
        exists ($p -> proj1_sig $h); exact (functorality_impl (proj2_sig $h))
      );
      iterate ()
  | [ |- { _ | _ -> forall _, _}] =>
      (* g is of form (forall x, P x) *)
      lazy_match! goal with 
      | [ |- { _ | _ -> ?g }] =>
          let p := get_all_pred g in
          let h_id := Fresh.in_goal @h in
          enough (forall x, sig (fun gx : Prop => gx -> $p x)) as $h_id;
          Control.focus 1 1 (fun () =>
            let h := Control.hyp h_id in
            exists (forall x, proj1_sig ($h x)); exact (functorality_forall (fun x => (proj2_sig ($h x))))
          );
          intro;
          iterate ()
      end
  | [ |- { _ | _ -> ex ?p }] =>
      (* g is of form (exists x, P x) *)
      let h_id := Fresh.in_goal @h in
      enough (forall x, sig (fun gx : Prop => gx -> $p x)) as $h_id;
      Control.focus 1 1 (fun () =>
        let h := Control.hyp h_id in
        exists (exists x, proj1_sig ($h x)); exact (functorality_exists (fun x => (proj2_sig ($h x))))
      );
      intro;
      iterate ()
  | [ |- { _ | _ -> _}] => Control.zero (PropagateNegationError
                           "Cannot propagate further.")
  end.


(** Tries to propagate the first negation in the goal backwards.
    Scenarios that are accounted for are those where the goal is the result
    of a negation being propagated forwards, e.g:
      ~ (P /\ Q) -> (P -> ~ Q), or 
      ~ (P /\ Q) -> (~P \/ ~Q).
*)
Ltac2 propagate_negation_backwards () :=
    (* Check whether goal is a proposition. *)
    let sort_goal := Aux.get_value_of_hyp (Control.goal ()) in
    match Aux.check_constr_equal sort_goal constr:(Prop) with
    | false => Control.zero (PropagateNegationError
                           "Can only propagate negation in propositions.")
    | true => 
        (* Preparation for recursive part. *)
        let h_id := Fresh.in_goal @h in
        ltac1:(h_id g |- transparent_assert_constr h_id (sig (fun new_g : Prop => new_g -> g)))
        (Ltac1.of_constr (ident_to_constr h_id)) (Ltac1.of_constr (Control.goal ()));
        Control.focus 1 1 (fun () => 
          (* Start recursive part *)
          iterate ()
        );
        (* Recursive part has been solved. Use its conclusion. *)
        let h := Control.hyp h_id in
        let new_g_name := Fresh.in_goal @new_g in
        enough (proj1_sig $h) as $new_g_name;
        Control.focus 1 1 (fun () => 
          let new_g := Control.hyp new_g_name in
          apply (proj2_sig $h); exact $new_g
        );
        simpl; clear h
    end.

