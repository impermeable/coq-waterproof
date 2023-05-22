Require Import Ltac2.Ltac2.

Require Import Util.Goals.

(**
  Defines a variable in an arbitrary goal.

  Arguments:
    - [u: constr], the name of the variable.
    - [t: constr], the variable to be defined.

  Does:
    - defines [t] as [u].
*)
Local Ltac2 defining (u: ident) (t: constr) :=
  set ($u := $t);
  let u_constr := Control.hyp u in 
  let w := Fresh.fresh (Fresh.Free.of_goal ()) @add_eq in
  assert ($w : $u_constr = $t) by reflexivity.
    


Ltac2 Notation "Define" u(ident) ":=" t(constr) :=
  panic_if_goal_wrapped ();
  defining u t.