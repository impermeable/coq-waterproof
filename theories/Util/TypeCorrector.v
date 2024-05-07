Require Import Util.Init.
Require Import Util.MessagesToUser.

From Ltac2 Require Import Ltac2 Message.

Local Ltac2 concat_list (ls : message list) : message :=
  List.fold_right concat (of_string "") ls.

(** Ensures that the type of [t] can be used in type matching or asserting. *)
Ltac2 correct_type_by_wrapping (t: constr): constr :=
  let type_t := Constr.type t in
  match! type_t with
    | Prop => t
    | Set => t 
    | Type => t
    | bool => constr:(is_true $t)
    | _ => throw (concat_list [
      of_string "Expected a term with type in ['Prop', 'Set', 'Type', 'bool'], but we got a term of type '";
      of_constr type_t; 
      of_string "' instead."]); constr:(tt)
  end.