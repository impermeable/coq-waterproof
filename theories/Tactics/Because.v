Require Import Ltac2.Ltac2.
Require Import Ltac2.Message.

Require Import Util.Goals.
Require Import Util.Hypothesis.

Local Ltac2 warn_wrong_prop_specified (user_type:constr) (coq_type:constr) := 
 match Constr.equal user_type coq_type with
    | true  => ()
    | false => 
      Control.zero
        (InputError (concat (concat (concat (of_string "Property ") (of_constr user_type)) 
        (concat (of_string " should be ") (of_constr coq_type))) (of_string ".")))
  end.

(**
  Destruct an AND hypothesis into its respective two parts if the types of the respective parts are correctly specified.

  Arguments:
    - [s: ident], the [ident] of the AND hypothesis.
    - [u: ident option], optional name of the first part of [s].
    - [tu : constr], specified type of the first part of [s].
    - [v: ident option], optional name of the second part of [s].
    - [tv : constr], specified type of the second part of [s].

  Does:
    - splits [s] into its two respective parts.

  Raises Exceptions:
    - [InputError] if the specified type [tu] or [tv] is not actually the type of [u] or [v] resp.
*)

Local Ltac2 and_hypothesis_destruct_with_types (s:ident) (u:ident option) (tu:constr) (v:ident option) (tv:constr) :=
  (* Copy hypothesis we will destruct. *)
  let s_val := Control.hyp s in
  let copy := Fresh.in_goal @copy in
  pose $s_val as copy;
  let copy_val := Control.hyp copy in
  (* Create identifiers if not specified. *)
  let uu := match u with
    | None   => Fresh.in_goal @__wp__hu
    | Some u => u
  end
  in
  let vv := match v with
    | None   => Fresh.in_goal @__wp__hv
    | Some v => v
  end
  in
  
  (* Destruct copy and check if types agree. *)
  destruct $copy_val as [$uu $vv];
  
  let type_u := get_value_of_hyp_id uu in
  warn_wrong_prop_specified tu type_u;

  let type_v := get_value_of_hyp_id vv in
  warn_wrong_prop_specified tv type_v.


Ltac2 Notation "Because" "(" s(ident) ")" "both" tu(constr) u(opt(seq("(", ident, ")"))) "and" tv(constr) v(opt(seq("(", ident, ")"))) w(opt("hold")) := 
  panic_if_goal_wrapped ();
  and_hypothesis_destruct_with_types s u tu v tv.


(**
  Destruct an OR hypothesis into its respective two parts if the types of the respective parts are correctly specified. Wraps the goal for both parts.

  Arguments:
    - [s: ident], the [ident] of the OR hypothesis.
    - [u: ident option], optional name of the first part of [s].
    - [tu : constr], specified type of the first part of [s].
    - [v: ident option], optional name of the second part of [s].
    - [tv : constr], specified type of the second part of [s].

  Does:
    - splits [s] into its two respective parts. Wraps the goal for both parts in the [Case.Wrapper] wrapper.
  
  Raises Exceptions:
    - [InputError] if the specified type [tu] or [tv] is not actually the type of [u] or [v] resp.
*)
Local Ltac2 or_hypothesis_destruct_with_types (s:ident) (u:ident option) (tu:constr) (v:ident option) (tv: constr) :=
  (* Copy hypothesis we will destruct. *)
  let s_val := Control.hyp s in
  let copy := Fresh.in_goal @copy in
  pose $s_val as copy;
  
  let copy_val := Control.hyp copy in
  (* Create identifiers if not specified. *)
  let uu := match u with
    | None   => Fresh.in_goal @__wp__hu
    | Some u => u
  end
  in
  let vv := match v with
    | None   => Fresh.in_goal @__wp__hv
    | Some v => v
  end
  in
  
  (* Destruct copy and check if types agree. *)
  destruct $copy_val as [$uu | $vv];
  Control.focus 1 1 (fun () =>
    let type_u := get_value_of_hyp_id uu in
    warn_wrong_prop_specified tu type_u;
    apply (Case.unwrap $type_u)
  );
  
  Control.focus 2 2 (fun () =>
    let type_v := get_value_of_hyp_id vv in
    warn_wrong_prop_specified tv type_v;
    apply (Case.unwrap $type_v)
  ).

Ltac2 Notation "Because" "(" s(ident) ")" "either" tu(constr) u(opt(seq("(", ident, ")"))) "or" tv(constr) v(opt(seq("(", ident, ")"))) w(opt("holds")) :=
  panic_if_goal_wrapped ();
  or_hypothesis_destruct_with_types s u tu v tv.
