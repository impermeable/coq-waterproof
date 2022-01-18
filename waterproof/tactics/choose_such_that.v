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
Require Import Waterproof.tactics.goal_wrappers.



(** * choose_destrct_without_extra_hypothesis
    Chooses a variable according to a particular definition, and label the remaining parts 
    of the definition.

    Arguments:
        - [s: ident], the variable to be chosen.
        - [v: constr], the definition used.
        - [u: ident], the remaining parts of the definition.

    Does:
        - destructs the constr [v] under the names [s] and [u].
*)

Ltac2 choose_destruct_without_extra_hypothesis (s:ident) (u:ident) (v:ident)
 := (* Copy hypothesis we will destruct. *)
    let v_val := Control.hyp v in
    let copy := Fresh.in_goal @copy in
    pose $v_val as copy;
    let copy_val := Control.hyp copy in
    destruct $copy_val as [$s $u].
(*
    (* Create identifiers if not specified. *)
    match u with
    | None   => let h := Fresh.in_goal @__wp__h in
                destruct $copy_val as [$s $h]
    | Some u => destruct $copy_val as [$s $u]
    end.
*)


Ltac2 Notation "Choose" s(ident) "such" "that" "("u(ident)")" "according" "to" "("v(ident)")"
 := panic_if_goal_wrapped ();
    choose_destruct_without_extra_hypothesis s u v.

(* Hard case from sup_and_inf.v

(** ## Suprema and sequences*)
Lemma seq_ex_almost_maximizer_ε :
  ∀ (a : ℕ → ℝ) (pr : has_ub a) (ε : ℝ), 
    ε > 0 ⇒ ∃ k : ℕ, a k > lub a pr - ε.
Proof.
    Take a : (ℕ → ℝ).
    Assume (has_ub a) (i).
    Expand the definition of lub.
    That is, write the goal as (for all ε : ℝ,  ε > 0 
      ⇨ there exists k : ℕ, a k > (let (a0, _) := ub_to_lub a (i) in a0) - ε).
    Define ii := (ub_to_lub a (i)).
    Choose l such that (H1) according to (ii).
    Take ε : ℝ; such that (ε > 0).
    By exists_almost_maximizer_ε it holds that (∃ y : ℝ, (EUn a) y ∧ y > l - ε) (iii).
    Choose y such that (iv) according to (iii).
    Because (iv) both (EUn a y) (v) and (y > l - ε).
    Expand the definition of EUn in (v).
    That is, write (v) as (there exists n : ℕ , y = a n).
    Choose n such that (H2) according to (v).
    Choose k := n.
    We need to show that (l - ε < a n).
    We conclude that (& l - ε &< y &= a n).
Qed.*)