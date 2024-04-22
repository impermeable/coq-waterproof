Require Import Util.Init.
Require Import Util.MessagesToUser.

From Ltac2 Require Import Ltac2 Message.

Local Ltac2 concat_list (ls : message list) : message :=
  List.fold_right concat (of_string "") ls.

(** Makes sure that we only ever try to assert a term of type `prop` *)
Ltac2 correct_type_for_assert (t: constr): constr :=
  let type_t := Constr.type t in
  match! type_t with
    | Prop => t
    | Set => t
    | Type => t
    | bool => constr:(is_true $t)
    | _ => throw (concat_list [of_string "Expected a term with 'assertable' type, but we got a term of type '"; of_constr type_t; of_string "' instead."]); constr:(tt)
  end.