Require Import Ltac2.Ltac2.
Require Import Ltac2.Message.

Require Import Util.Goals.

Ltac2 Type exn ::= [ ChooseError(string) | ChooseSuchThatError(message) ].


(** * Choose *)

(**
    
  Instantiate a variable in an [exists] [goal], according to a given [constr], and also renames the [constr].

  Arguments:
    - [s: ident], an [ident] for naming an idefined [constr]/variable.
    - [t: constr], the requirted [constr] that needs to be instantiated.

  Does:
    - instantiates the [constr] [t] under the name [s].

  Raises Exceptions:
    - [ChooseError], if the [goal] is not an [exists] [goal].
*)
Ltac2 choose_variable_in_exists_goal_with_renaming (s:ident) (t:constr) :=
  lazy_match! goal with
    | [ |- exists _ : _, _] =>
      pose ($s := $t);
      let v := Control.hyp s in
      let w := Fresh.fresh (Fresh.Free.of_goal ()) @add_eq in
      exists $v;
      assert ($w : $v = $t) by reflexivity
    | [ |- _ ] => Control.zero (ChooseError "`Choose` can only be applied to 'exists' goals")
  end.



(**
  Instantiate a variable in an [exists] [goal], according to a given [constr], without renaming said [constr].

  Arguments:
    - [t: constr], the requirted [constr] that needs to be instantiated.

  Does:
    - instantiates the [constr] [t] under the same name.

  Raises Exceptions:
    - [ChooseError], if the [goal] is not an [exists] [goal].
*)
Ltac2 choose_variable_in_exists_no_renaming (t:constr) :=
    lazy_match! goal with
        | [ |- exists _ : _, _] => exists $t
        | [ |- _ ] => Control.zero (ChooseError "`Choose` can only be applied to 'exists' goals")
    end.

Ltac2 Notation "Choose" s(opt(seq(ident, ":="))) t(constr) :=
  panic_if_goal_wrapped ();
  match s with 
    | None => choose_variable_in_exists_no_renaming t
    | Some s => choose_variable_in_exists_goal_with_renaming s t
  end.


(** * Choose such that *)

Local Ltac2 mismatch_pred_existential_message (s : ident) (v : ident) :=
  concat (concat
    (concat (of_string "Claimed property of ") (of_ident s))
    (concat (of_string " does not match ‘there exists’-statement (") (of_ident v))) (of_string ").").


(** *
  Chooses a variable according to a particular hypothesis and labels the remaining parts of the definition.

  Arguments:
    - [s: ident], the name of the variable to be chosen.
    - [v: ident], the hypothesis used.
    - [pred_u: constr], predicate that should hold for [s] and [v]'s type should match (ex [pred_u]) or (sig [pred_u]).
    - [u: ident option], optional name of property that [s] is to satisfy.
  Does:
    - Destructs the constr [v] under the names [s] (and [u]).
    - Copies the hypothesis [v] to a new hypothesis also called [v], hence the hypothesis is preserved despite its destruction.

  Raises exceptions:
    - [ChooseSuchThatError], if [v]'s type does not match (ex [pred_u]) or (sig [pred_u]).
*)

Ltac2 choose_such_that (s:ident) (v:ident) (pred_u:constr) (u:ident option) :=
  let v_val := Control.hyp v in
  let copy_id := Fresh.in_goal @copy in
  (* Create identifier if u is not specified. *)
  let uu := match u with
    | None   => Fresh.in_goal @__wp__h
    | Some u => u
  end in
  match Control.case (fun () =>
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
      ) (fun e =>
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

Ltac2 Notation "Obtain" s(ident) "according" "to" "("v(ident)")" "," "so" pred_u(constr) u(opt(seq("(", ident, ")"))) := 
  panic_if_goal_wrapped ();
  choose_such_that s v pred_u u.
  
