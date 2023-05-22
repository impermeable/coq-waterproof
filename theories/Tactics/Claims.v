Require Import Ltac2.Ltac2.

Require Import Util.Constr.
Require Import Util.Goals.

Local Ltac2 my_assert (t:constr) (id:ident option) := 
  match id with
    | None =>
      let h := Fresh.in_goal @__wp__h in
      ltac2_assert h t
    | Some id => ltac2_assert id t
  end.

Ltac2 Notation "We" "claim" "that" t(constr) id(opt(seq("(", ident, ")"))) :=
  panic_if_goal_wrapped ();
  my_assert t id.