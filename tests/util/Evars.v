Require Import Ltac2.Ltac2.
Require Import Waterproof.Waterproof.
Require Import Waterproof.Util.Evars.

(** Test 1 : Test that rename_blank_evars_in_term introduces an evar
    and names it correctly. *)
Goal True.
rename_blank_evars_in_term "a" open_constr:(_).
 (* Check whether ?a is defined*)
(fun _ => ()) (Constr.type constr:(?a)).
(* Indeed, the same statement doesn't work with b *)
Fail (fun _ => ()) (Constr.type constr:(?b)).
Abort.

(** Test 2 : Test that rename_blank_evars_in_term introduces evars deriving their 
    type from the plus operator, and names them correctly
*)
Goal True.
Proof.
rename_blank_evars_in_term "c" open_constr:(_ + _).
assert (?c + ?c0 = 0). (* Fails if [c] and [c0] are not defined. *)
Abort.

(** Test 3 : Test with a complicated expression *)
Goal True.
Proof.
rename_blank_evars_in_term "d"
  open_constr:(forall _ : _, (fun _ _ _ => _) _ _ _ + _ _ = _ _).
(fun _ => ()) (Constr.type constr:(?d6)).
(* cannot use ?d now because we're not in the right context *)
Fail (fun _ => ()) (Constr.type constr:(?d)).
Abort.

(** Test 4 : Rename the evar corresponding to the current goal *)
Goal True.
Proof.
refine_goal_with_evar "my_goal_name".
(fun _ => ()) (Constr.type constr:(?my_goal_name)).
Abort.

(** Test 5 : Rename the evar corresponding to the current goal, and then shelve it *)
Goal True.
refine_goal_with_evar "my_goal_name".
Control.shelve().
Abort.
