From mathcomp Require Import ssreflect ssrbool eqtype.

From Ltac2 Require Import Ltac2 Message.

Ltac2 try_hypotheses () :=
    match! goal with
    | [ h : is_true (?i == ?j) |- _ ] => 
        let h := Control.hyp h in rewrite $h
    | [ h : ?i == ?j = false |- _ ] => 
        let h := Control.hyp h in rewrite $h    
    | [ h : is_true (?i != ?j) |- _ ] => 
        let h := Control.hyp h in
        let h_id := Fresh.in_goal @_temp in
        let do_assert () := (assert (($i == $j) = false) as $h_id by (apply negbTE; exact $h)) in
        let do_rewrite () := (let h_val := Control.hyp h_id in rewrite $h_val; clear $h_id) in
        do_assert ();
        do_rewrite ()
    end.

Ltac2 simplify_if () := 
    first [
        ltac1:(rewrite eq_refl) |
        try_hypotheses ()
    ].

#[export] Hint Extern 1 => ltac2:(simplify_if ()) : wp_algebra.
