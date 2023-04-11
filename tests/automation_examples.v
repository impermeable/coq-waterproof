Require Import Waterproof.AllTactics.
Require Import Waterproof.notations.notations.
Require Import Waterproof.load.
Module Import db_RealsAndIntegers := databases(RealsAndIntegers).
Require Import Waterproof.set_debug_level.Info.

Set Default Timeout 4.

Require Import Reals.
Open Scope R_scope.
Check -1.
Locate "1".
Local Parameter f : R -> R -> R.
Locate "_ - _".
Print Rminus.

(** ** TODO: what would be the appropriate cost here? 
    It seems this one is necessary. Add to appropriate 
    place at hint database? *)
Local Hint Extern 0 => unfold Rminus : wp_reals.

Local Parameter g : R -> R.
Local Parameter g_monotone : forall x y : R, x < y -> g x < g y.
Local Parameter h : R -> R.
Local Parameter h_monotone : forall x y : R, x <= y -> h x <= h y.

Goal forall a b : R, a <= b -> 4 + h a <= 5 + h b.
Proof.
Take a, b : R.
Assume that (a <= b).
Search ( _ <= _ -> _ + _ <= _ + _).
(** TODO: why does this needs to be added to the database still 
    to make the below line work? *)
Local Hint Resolve Rplus_le_compat : wp_reals.
(** Question: Is the 'using' only tried in the beginning??
    Doesn't seem so if I read the documentation... *)
ltac1:(debug auto using h_monotone with real wp_reals).
Abort.

Goal forall a b : R, a < b -> 4 + g a < 5 + g b.
Proof.
Take a, b : R.
Assume that (a < b).
We conclude that (4 + g a < 5 + g b).
Abort.


Goal forall a b : R, a < b -> 4 + g a < 4 + g b.
Proof.
Take a, b : R.
Assume that (a < b).
We conclude that (4 + g a < 4 + g b).
Abort.

Lemma strange_error (a c : R):
    a = - c -> 0 <= c -> | a | = c.
Proof.
  intros a_eq_min_c.
  intros zero_le_c.
  rewrite a_eq_min_c.
  (* unfold Rabs; destruct (Rcase_abs).*)
  ltac1:(info_auto with wp_reals).
  (** Strange error, possibly because nothing is done with b*)
  We conclude that ( | - c | = c ).
Qed.


Lemma help_out_with_abs (a c : R):
    a = - c -> 0 <= c -> | a | = c.
Proof.
intros a_eq_min_c.
intros zero_le_c.
rewrite a_eq_min_c.
(** This should work *)
We conclude that ( | - c | = c ).
Qed.

Require Import Waterproof.set_search_depth.To_3.

Goal forall r : R, r > 0 -> 0 < | r / 2 |.
Proof.
Take r : R.
Assume that (r > 0).
We conclude that (& 0 < r / 2 = | r / 2| ).
Qed.

Goal forall x r : R, r > 0 ->
    x = Rmax(0, 1 - r/2) -> | x - 1 | < r.
Proof.
Take x, r : R.
Assume that (r > 0).
Assume that (x = Rmax(0, 1 - r/2)).
(** There is an issue here that Waterproof doesn't 
    indicate which inequality doesn't hold. 
    The lines below should work. *)
We conclude that
    (& | x - 1 | = | Rmax(0, 1-r/2) - 1 |
                 = 1 - Rmax(0, 1 - r/2)
                 <= 1 - (1 - r/2)
                 < r ).
(** The lines below should work. *)                
It holds that 
    (& | x - 1 | = | Rmax(0, 1-r/2) - 1 |
                 = 1 - Rmax(0, 1 - r/2)
                 <= 1 - (1 - r/2)
                 < r ).
(** Apparently one of the difficulties is in this step. *)
We claim that ( | Rmax(0, 1-r/2) - 1 |
                 = 1 - Rmax(0, 1 - r/2) ).
{
    Set Default Timeout 1.
    (* ltac1:(debug auto 3 using help_out_with_abs with real wp_reals). *)
    ltac1:(simple apply help_out_with_abs).
    * auto with real.

    (** This should also work ... *)
    It suffices to show that ( 1 - Rmax(0, 1 - r/2) >= 0).
    (** This should work ... *)
    It suffices to show that ( Rmax(0, 1 - r/2) - 1 <= 0).
    (** We add the lemma defined in the preamble, but
        it still doesn't work *)
    We conclude that
        ( | Rmax(0, 1 - r/2) - 1 | = 1 - Rmax(0, 1 - r/2) ).
    By help_out_with_abs it suffices to show that
        ( 1 - Rmax(0, 1 - r/2) >= 0 ).
    (** This should work again ...*)
    
    We conclude that 
        (& 1 - Rmax(0, 1 - r/2) >= 1 - 1 = 0).
}

ltac1:(autoapply with real wp_reals).

Qed.

Require Import Waterproof.set_search_depth.To_5.
(** ** It is somehow difficult to deal with zeros ...*)
Goal forall r : R, r > 0 ->
    0 <= 1 - Rmax( 0, 1 - r/2 ).
Proof.
    intros r r_gt_0.
(** It would be nice if this can be proved automatically, 
    but we need a chain of inequalities for this... *)
    We conclude that 
    (& 0 <= 1 - 1 <= 1 - Rmax(0, 1 - r/2) ).
(** Although there is also something to say for students 
    needing to do this ... *)
Qed.

Goal forall b: R, b > 0 -> - Rmax( 0, 1 - b/2) >= - 1.
Proof.
intros b b_gt_0.
(** It is weird that the following line gives an error *)
ltac1:(simple apply Ropp_le_ge_contravar).
(** I don't know what the -1 really represents at the end. *)
(* Unset Printing Notations.
Unset Printing Coercions. *)
(** Especially after this: *)
change (- Rmax(0 , 1 - b/2) >= - 1%R).
ltac1:(simple apply Ropp_le_ge_contravar).
ltac1:(info_auto with real wp_reals).
Qed.


(** * Attempts to make Rmax and Rabs transparent to lra and nra. *)

Require Import Waterproof.set_search_depth.To_3.
Local Hint Extern 0 => 
    unfold Rabs;
    destruct (Rcase_abs) : wp_reals.
Local Hint Extern 0 => unfold Rmax;
    destruct (Rle_dec) : wp_reals.

(** This is an example to show that 
    lra can manipulate logical expressions ... *)
Goal (forall a b : R, a < 5 -> b < 5 -> 
  (a < 3) \/ (b < 3) -> a + b < 8).
Proof.
intros a b.
ltac1:(Lra.lra).
Qed.

Goal forall a b c: R, (a <= b -> c = b) 
    /\ (b <= a -> c = a) -> b <= c.
Proof.
  intros a b c H.
  ltac1:(Lra.lra).
Qed.

Goal forall b: R, b > 0 -> - Rmax( 0, 1 - b/2) >= - 1.
Proof.
intros b b_gt_0.
unfold Rmax.
destruct (Rle_dec).
ltac1:(Lra.lra).
ltac1:(Lra.lra).
Qed.

(** In fact this is relatively easily solved 
    by unfolding Rmax and Rabs and destructing ... *)
Goal forall r : R, r > 0 -> 
| Rmax(0, 1-r/2) - 1 |
                 = 1 - Rmax(0, 1 - r/2).
Proof.
intros r r_gt_0.
unfold Rabs.
unfold Rmax.
destruct (Rcase_abs).
destruct (Rle_dec).
ltac1:(Lra.lra).
ltac1:(Lra.lra).
destruct (Rle_dec).
ltac1:(Lra.lra).
ltac1:(Lra.lra).
Qed.

Goal forall r : R, r > 0 -> 
| Rmax(0, 1-r/2) - 1 |
                 = 1 - Rmax(0, 1 - r/2).
Proof.
intros r r_gt_0.
ltac1:(info_auto with wp_reals).
Qed.

Goal forall x r : R, r > 0 ->
    x = Rmax(0, 1 - r/2) -> | x - 1 | < r.
Proof.
Take x, r : R.
Assume that (r > 0).
Assume that (x = Rmax(0, 1 - r/2)).
(** There is an issue here that Waterproof doesn't 
    indicate which inequality doesn't hold. 
    The lines below should work. *)
(*
This would already work, which is very strong ... :    
We conclude that (& | x - 1| = | Rmax(0, 1-r/2) - 1 | < r ). *)
We conclude that
    (& | x - 1 | = | Rmax(0, 1-r/2) - 1 |
                 = 1 - Rmax(0, 1 - r/2)
                 <= 1 - (1 - r/2)
                 < r ).
Qed.

(** Question: what happens if there 
    are more absolute values and Rmax's in the equation? *)
